import Clean.Bellman.TopLevel
import Mathlib.Data.ZMod.Defs

/-!
Pins top-level circuits, from a private value to the relation on public inputs:

- a square: a private `x`, the public input `y = x · x` and the row `x · x = y`, with the
  statement that `y` is the square of the private witness. The key's rows are that row and one
  appended row for each of ONE and `y`; an assignment satisfying them has `y = aux 0 ^ 2`, so over
  `ZMod 7` the relation rejects `[3]`, and it rejects the wrong number of inputs; public inputs in
  it are the typed public input's elements; the prover's public inputs are in it and are
  `[x · x]`, and its private value is `x`;
- a parent built from calls: a private bit (`AllocatedBit::alloc`), then a private value made
  public (`AllocatedNum::alloc`, `inputize`), made top-level from the children's independence
  alone, with the children's prover-side assumptions and specs as its own. Its statement: the
  private bit is boolean and the public input is the private value. The prover's public input is
  the value;
- a public input of two elements: field `k` reads input `k + 1`;
- a circuit with no public inputs: the relation holds exactly at `[]`.
-/

namespace Bellman.Tests.TestTopLevel
open Bellman

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable {F : Type} [Field F]

/-! ## A square -/

/-- One public field element. -/
structure Single (F : Type) where
  y : F

instance : ProvableType Single where
  size := 1
  toElements p := #v[p.y]
  fromElements v := ⟨v[0]⟩
  toElements_fromElements v := by
    rw [Vector.ext_iff]; intro i hi
    obtain rfl : i = 0 := by omega
    rfl
  fromElements_toElements _ := rfl

def squareMain (w : Option F) : Circuit F (Variable × Variable) := do
  let x ← alloc "x" fun _ => w.getD 0
  let y ← allocInput "y" fun env => env.toEnvironment.get x * env.toEnvironment.get x
  enforce "square" (· + x) (· + x) (· + y)
  pure (x, y)

/-- A private `x`, the public input `y = x · x`, and the row `x · x = y`. The output names both,
so that the statement can read the private one. -/
def square : FormalCircuit F (Option F) (Variable × Variable) where
  main := squareMain
  rowsAt _ o := [⟨(LinearCombination.zero : LinearCombination F) + (⟨.aux o.aux⟩ : Variable),
    (LinearCombination.zero : LinearCombination F) + (⟨.aux o.aux⟩ : Variable),
    (LinearCombination.zero : LinearCombination F) + (⟨.input o.input⟩ : Variable)⟩]
  output _ o := (⟨.aux o.aux⟩, ⟨.input o.input⟩)
  nextOffset _ o := ⟨o.input + 1, o.aux + 1⟩
  computable _ o _ _ := ⟨fun _ _ _ => rfl, fun e e' he => by
    have hx := Variable.get_agrees (v := ⟨.aux o.aux⟩) (o := ⟨o.input, o.aux + 1⟩)
      (show o.aux < o.aux + 1 by omega) he
    simp only [hx], trivial⟩
  output_below _ o _ := ⟨show o.aux < o.aux + 1 by omega, show o.input < o.input + 1 by omega⟩
  Spec env _ xy := env.get xy.2 = env.get xy.1 ^ 2
  ProverSpec env w xy := env.toEnvironment.get xy.1 = w.getD 0
  soundness := by
    intro o env w _ _ h
    simp only [List.mem_singleton, forall_eq, circuit_norm, zero_add] at h
    show env.input o.input = env.aux o.aux ^ 2
    rw [← h, pow_two]
  completeness := by
    intro o env w _ _ _ hw
    simp only [squareMain, circuit_norm, List.append_nil, List.singleton_append] at hw
    simp only [List.mem_singleton, forall_eq, circuit_norm, zero_add]
    exact ⟨hw.2.symm, hw.1⟩

def squareTop : TopLevelCircuit F F (Variable × Variable) Single where
  formalCircuit := square
  indep := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  assumptions_eq := rfl
  numInputs_eq := rfl
  PrivateWitness := F
  extractPrivate env := env.aux 0
  Spec p x := p.y = x ^ 2
  spec_of _ _ h := h

-- the key's rows: the circuit's one row, then one appended row for each of ONE and `y`
example : ((squareTop (F := ZMod 7)).formalCircuit.rowsAt none Offset.start).length = 1 ∧
    (squareTop (F := ZMod 7)).numInputs = 2 ∧ (squareTop (F := ZMod 7)).keyRows.length = 3 := by
  decide

-- an assignment with inputs `(1, y)` satisfying the key's rows has `y` the square of the private
-- witness it holds
example (y : F) (aux : ℕ → F)
    (h : ∀ r ∈ (squareTop (F := F)).keyRows, r.Holds (withPublic [y] aux)) : y = aux 0 ^ 2 :=
  squareTop.soundness [y] aux h

-- over `ZMod 7`, 3 is not a square, so `[3]` is not in the relation
example : ¬ (squareTop (F := ZMod 7)).Relation [3] := by
  intro h
  have h' : ∃ x : ZMod 7, (3 : ZMod 7) = x ^ 2 :=
    (squareTop (F := ZMod 7)).statement_soundness [3] h
  obtain ⟨x, hx⟩ := h'
  revert hx; revert x; decide

-- public inputs in the relation are the typed public input's elements
example (y : F) (h : (squareTop (F := F)).Relation [y]) :
    (toElements (readPublicInput (PublicInput := Single) [y])).toList = [y] :=
  squareTop.toElements_readPublicInput [y] h

-- the wrong number of public inputs is not in the relation
example (a b : F) :
    ¬ (squareTop (F := F)).Relation [] ∧ ¬ (squareTop (F := F)).Relation [a, b] := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> exact absurd h.1
    (by simp [TopLevelCircuit.numInputs, squareTop, square, Offset.start])

-- the prover's public inputs are in the relation and are `[x · x]`, and its private value is `x`
example (hint : ProverHint F) (x : F) :
    (squareTop (F := F)).Relation
      ((((squareTop (F := F)).formalCircuit.main (some x)).operations Offset.start).compute hint
        ([1], [])).1.tail ∧
    ((((squareTop (F := F)).formalCircuit.main (some x)).operations Offset.start).compute hint
        ([1], [])).1.tail = [x * x] ∧
    ((squareTop (F := F)).formalCircuit.computedEnv hint (some x) Offset.start [1] []).aux 0
      = x :=
  ⟨(squareTop.completeness hint x trivial).1, rfl, (squareTop.completeness hint x trivial).2⟩

/-! ## A parent built from calls -/

/-- `AllocatedBit::alloc` (`boolean.rs:70-99`): the value is captured, `none` at key
generation. -/
def allocBit : FormalCircuit F (Option Bool) Variable where
  main v := do
    let a ← alloc "boolean" fun _ => if v.getD false then 1 else 0
    enforce "boolean constraint" (· + one - a) (· + a) id
    pure a
  rowsAt _ o := [⟨LinearCombination.zero + one - (⟨.aux o.aux⟩ : Variable),
    LinearCombination.zero + (⟨.aux o.aux⟩ : Variable), LinearCombination.zero⟩]
  output _ o := ⟨.aux o.aux⟩
  nextOffset _ o := { o with aux := o.aux + 1 }
  computable _ _ _ _ := ⟨fun _ _ _ => rfl, trivial⟩
  output_below _ o _ := by show o.aux < o.aux + 1; omega
  Spec env _ a := env.get a = 0 ∨ env.get a = 1
  soundness := by
    intro o env v h1 _ h
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, circuit_norm, h1] at h ⊢
    rcases mul_eq_zero.1 h with h | h
    · right; exact (sub_eq_zero.1 h).symm
    · left; exact h
  completeness := by
    intro o env v h1 _ _ h
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, circuit_norm, h1] at h ⊢
    rw [h]; split <;> simp

/-- `AllocatedNum::alloc` (`num.rs:26-47`) on a captured value, then `inputize`
(`num.rs:49-63`). Rust's `inputize` returns `()`; this returns both variables, so that the spec
(which does not see the offset) can name them. -/
def pubMain (val : Option F) : Circuit F (Variable × Variable) := do
  let x ← alloc "num" (fun _ => val.getD 0)
  let y ← allocInput "input variable" (fun env => env.toEnvironment.get x)
  enforce "enforce input is correct" (· + y) (· + one) (· + x)
  pure (x, y)

def pub : FormalCircuit F (Option F) (Variable × Variable) where
  main := pubMain
  rowsAt _ o :=
    [⟨(LinearCombination.zero : LinearCombination F) + (⟨.input o.input⟩ : Variable),
    (LinearCombination.zero : LinearCombination F) + one,
    (LinearCombination.zero : LinearCombination F) + (⟨.aux o.aux⟩ : Variable)⟩]
  output _ o := (⟨.aux o.aux⟩, ⟨.input o.input⟩)
  nextOffset _ o := ⟨o.input + 1, o.aux + 1⟩
  computable _ o _ _ := ⟨fun _ _ _ => rfl, fun _ _ he => he.2.1 o.aux (by simp), trivial⟩
  output_below _ o _ := ⟨show o.aux < o.aux + 1 by omega, show o.input < o.input + 1 by omega⟩
  Spec env _ xy := env.get xy.2 = env.get xy.1
  soundness := by
    intro o env _ h1 _ h
    simp only [List.mem_singleton, forall_eq, circuit_norm, zero_add, h1, mul_one] at h ⊢
    exact h
  completeness := by
    intro o env _ h1 _ _ hw
    simp only [pubMain, circuit_norm, List.append_nil, List.cons_append,
      List.nil_append] at hw
    simp only [List.mem_singleton, forall_eq, circuit_norm, zero_add, h1, mul_one]
    exact hw.2

section Pair

variable (B : FormalCircuit F (Option Bool) Variable)
  (P : FormalCircuit F (Option F) (Variable × Variable))

/-- `B` on the private bit, then `P` on the private value, each through a call. -/
def pairMain (w : Option (Bool × F)) : Circuit F (Variable × (Variable × Variable)) := do
  let b ← B.call (w.map Prod.fst)
  let p ← P.call (w.map Prod.snd)
  pure (b, p)

def pair (hAB : B.Assumptions = fun _ _ => True) (hAP : P.Assumptions = fun _ _ => True) :
    FormalCircuit F (Option (Bool × F)) (Variable × (Variable × Variable)) where
  main := pairMain B P
  rowsAt w o := B.rowsAt (w.map Prod.fst) o ++
    P.rowsAt (w.map Prod.snd) (B.nextOffset (w.map Prod.fst) o)
  rowsAt_eq w o := by simp only [pairMain, circuit_norm]
  output w o := (B.output (w.map Prod.fst) o,
    P.output (w.map Prod.snd) (B.nextOffset (w.map Prod.fst) o))
  output_eq w o := by simp only [pairMain, circuit_norm]
  nextOffset w o := P.nextOffset (w.map Prod.snd) (B.nextOffset (w.map Prod.fst) o)
  nextOffset_eq w o := by simp only [pairMain, circuit_norm]
  advance_eq w o := by simp only [pairMain, circuit_norm]
  computable w o ho _ := by
    simp only [pairMain, circuit_norm]
    exact ⟨B.computable_call _ o ho trivial, P.computable_call _ _
      (Nat.lt_of_lt_of_le ho (B.le_nextOffset _ o).1) trivial⟩
  output_below w o _ := ⟨HasBelow.mono (B.output_below _ o trivial)
      (P.le_nextOffset _ _).1 (P.le_nextOffset _ _).2,
    P.output_below _ _ trivial⟩
  Spec env w bp := B.Spec env (w.map Prod.fst) bp.1 ∧ P.Spec env (w.map Prod.snd) bp.2
  ProverAssumptions env w := B.ProverAssumptions env (w.map Prod.fst) ∧
    P.ProverAssumptions env (w.map Prod.snd)
  ProverSpec env w bp := B.ProverSpec env (w.map Prod.fst) bp.1 ∧
    P.ProverSpec env (w.map Prod.snd) bp.2
  soundness o env w h1 _ h :=
    ⟨B.soundness o env _ h1 (by rw [hAB]; trivial) fun r hr => h r (List.mem_append_left _ hr),
      P.soundness _ env _ h1 (by rw [hAP]; trivial) fun r hr => h r (List.mem_append_right _ hr)⟩
  completeness o env w h1 _ hW h := by
    simp only [pairMain, circuit_norm] at h
    obtain ⟨rB, sB⟩ := B.completeness_call o env _ h1 (by rw [hAB]; trivial) hW.1 h.1
    obtain ⟨rP, sP⟩ := P.completeness_call _ env _ h1 (by rw [hAP]; trivial) hW.2 h.2
    refine ⟨fun r hr => ?_, sB, sP⟩
    rcases List.mem_append.1 hr with hr | hr
    · exact rB r hr
    · exact rP r hr

/-- The parent's independence of the private data, from the children's alone. -/
theorem pair_indep (hAB : B.Assumptions = fun _ _ => True) (hAP : P.Assumptions = fun _ _ => True)
    (iB : B.Indep) (iP : P.Indep) : (pair B P hAB hAP).Indep where
  rows w w' o := by
    show _ ++ _ = _ ++ _
    rw [iB.rows _ (w'.map Prod.fst), iB.nextOffset _ (w'.map Prod.fst),
      iP.rows _ (w'.map Prod.snd)]
  output w w' o := by
    show (_, _) = (_, _)
    rw [iB.output _ (w'.map Prod.fst), iB.nextOffset _ (w'.map Prod.fst),
      iP.output _ (w'.map Prod.snd)]
  nextOffset w w' o := by
    show P.nextOffset _ _ = P.nextOffset _ _
    rw [iB.nextOffset _ (w'.map Prod.fst), iP.nextOffset _ (w'.map Prod.snd)]

end Pair

/-- The parent's independence, from the children's. -/
theorem pairBitPub_indep : (pair (F := F) allocBit pub rfl rfl).Indep :=
  pair_indep allocBit pub rfl rfl ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

def pairTop : TopLevelCircuit F (Bool × F) (Variable × (Variable × Variable)) Single where
  formalCircuit := pair allocBit pub rfl rfl
  indep := pairBitPub_indep
  assumptions_eq := rfl
  numInputs_eq := rfl
  PrivateWitness := F × F
  extractPrivate env := (env.aux 0, env.aux 1)
  Spec p bv := (bv.1 = 0 ∨ bv.1 = 1) ∧ p.y = bv.2
  spec_of _ _ h := h

-- the key's rows: the two children's rows, then one appended row for each of ONE and the value
example : ((pairTop (F := ZMod 7)).formalCircuit.rowsAt none Offset.start).length = 2 ∧
    (pairTop (F := ZMod 7)).numInputs = 2 ∧ (pairTop (F := ZMod 7)).keyRows.length = 4 := by
  decide

-- an assignment with inputs `(1, y)` satisfying the key's rows: the bit (aux 0) is boolean, and
-- `y` is the value (aux 1)
example (y : F) (aux : ℕ → F)
    (h : ∀ r ∈ (pairTop (F := F)).keyRows, r.Holds (withPublic [y] aux)) :
    (aux 0 = 0 ∨ aux 0 = 1) ∧ y = aux 1 :=
  pairTop.soundness [y] aux h

-- for every private bit and value, the prover's public inputs are in the relation, and are the
-- value
example (hint : ProverHint F) (b : Bool) (v : F) :
    (pairTop (F := F)).Relation
      ((((pairTop (F := F)).formalCircuit.main (some (b, v))).operations Offset.start).compute
        hint ([1], [])).1.tail ∧
    ((((pairTop (F := F)).formalCircuit.main (some (b, v))).operations Offset.start).compute
        hint ([1], [])).1.tail = [v] := by
  refine ⟨(pairTop.completeness hint (b, v) ⟨trivial, trivial⟩).1, ?_⟩
  simp only [pairTop, pair, pairMain, circuit_norm, FormalCircuit.operations_call]
  rfl

/-! ## Two public inputs -/

/-- Two public field elements. -/
structure Two (F : Type) where
  a : F
  b : F

instance : ProvableType Two where
  size := 2
  toElements p := #v[p.a, p.b]
  fromElements v := ⟨v[0], v[1]⟩
  toElements_fromElements v := by
    rw [Vector.ext_iff]; intro i hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> rfl
  fromElements_toElements _ := rfl

-- field `k` of the public input reads input `k + 1`, after ONE
example : let p : Two (ZMod 7) :=
      extractPublicInput (⟨fun i => (i : ZMod 7), fun _ => 0⟩ : Environment (ZMod 7))
    p.a = 1 ∧ p.b = 2 := by
  decide

/-! ## No public inputs -/

/-- A private bit, with no public input (`unit`): the statement is that some private value is a
bit. -/
def bitTop : TopLevelCircuit F Bool Variable unit where
  formalCircuit := allocBit
  indep := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  assumptions_eq := rfl
  numInputs_eq := rfl
  PrivateWitness := F
  extractPrivate env := env.aux 0
  Spec _ b := b = 0 ∨ b = 1
  spec_of _ _ h := h

-- with no public input, the relation holds at `[]`, and only there
example : (bitTop (F := F)).Relation [] ∧ ∀ a : F, ¬ (bitTop (F := F)).Relation [a] := by
  refine ⟨(bitTop.completeness (fun _ _ => #[]) true trivial).1, fun a h => ?_⟩
  exact absurd h.1
    (by simp [TopLevelCircuit.numInputs, bitTop, allocBit, Offset.start])

end Bellman.Tests.TestTopLevel
