import Clean.Bellman.TopLevel
import Mathlib.Data.ZMod.Defs

/-!
Pins top-level circuits, from a private value to the relation on public inputs:

- a square: a private `x`, the public input `y = x · x` and the row `x · x = y`. The key's rows
  are that row and one appended row for each of ONE and `y`; the relation forces `y` to be a
  square, so over `ZMod 7` it rejects `[3]`, and it rejects the wrong number of inputs; the
  prover's public inputs are in it and are `[x · x]`;
- a parent built from calls: a private bit (`AllocatedBit::alloc`), then a private value made
  public (`AllocatedNum::alloc`, `inputize`), made top-level from the children's independence
  alone, with the children's prover-side assumptions and specs as its own. The relation forces
  the bit to be boolean and the public input to be the value, and the prover's public input is
  the value;
- a circuit with no public inputs: the relation holds exactly at `[]`.
-/

namespace Bellman.Tests.TestTopLevel
open Bellman

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable {F : Type} [Field F]

/-! ## A square -/

def squareMain (w : Option F) : Circuit F Variable := do
  let x ← alloc "x" fun _ => w.getD 0
  let y ← allocInput "y" fun env => env.toEnvironment.get x * env.toEnvironment.get x
  enforce "square" (· + x) (· + x) (· + y)
  pure y

/-- A private `x`, the public input `y = x · x`, and the row `x · x = y`. -/
def square : FormalCircuit F (Option F) Variable where
  main := squareMain
  rowsAt _ o := [⟨(LinearCombination.zero : LinearCombination F) + (⟨.aux o.aux⟩ : Variable),
    (LinearCombination.zero : LinearCombination F) + (⟨.aux o.aux⟩ : Variable),
    (LinearCombination.zero : LinearCombination F) + (⟨.input o.input⟩ : Variable)⟩]
  output _ o := ⟨.input o.input⟩
  nextOffset _ o := ⟨o.input + 1, o.aux + 1⟩
  computable _ o _ _ := ⟨fun _ _ _ => rfl, fun e e' he => by
    have hx := Variable.get_agrees (v := ⟨.aux o.aux⟩) (o := ⟨o.input, o.aux + 1⟩)
      (show o.aux < o.aux + 1 by omega) he
    simp only [hx], trivial⟩
  output_below _ o _ := by show o.input < o.input + 1; omega
  Spec env _ y := ∃ x : F, env.get y = x ^ 2
  soundness := by
    intro o env w _ _ h
    simp only [List.mem_singleton, forall_eq, circuit_norm, zero_add] at h
    exact ⟨env.aux o.aux, by show env.input o.input = _; rw [← h, pow_two]⟩
  completeness := by
    intro o env w _ _ _ hw
    simp only [squareMain, circuit_norm, List.append_nil, List.singleton_append] at hw
    simp only [List.mem_singleton, forall_eq, circuit_norm, zero_add]
    exact hw.2.symm

def squareTop : TopLevelCircuit F F Variable :=
  .ofIndep square ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩ rfl

-- the key's rows: the circuit's one row, then one appended row for each of ONE and `y`
example : ((squareTop (F := ZMod 7)).formalCircuit.rowsAt none Offset.start).length = 1 ∧
    (squareTop (F := ZMod 7)).numInputs = 2 ∧ (squareTop (F := ZMod 7)).keyRows.length = 3 := by
  decide

-- public inputs `[y]` in the relation make `y` a square
example (y : F) (h : (squareTop (F := F)).Relation [y]) : ∃ x : F, y = x ^ 2 := by
  obtain ⟨aux, x, hx⟩ := squareTop.soundness [y] h
  exact ⟨x, hx⟩

-- over `ZMod 7`, 3 is not a square, so `[3]` is not in the relation
example : ¬ (squareTop (F := ZMod 7)).Relation [3] := by
  intro h
  obtain ⟨aux, x, hx⟩ := squareTop.soundness [3] h
  revert hx; change (3 : ZMod 7) = x ^ 2 → False; revert x; decide

-- the wrong number of public inputs is not in the relation
example (a b : F) :
    ¬ (squareTop (F := F)).Relation [] ∧ ¬ (squareTop (F := F)).Relation [a, b] := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> exact absurd h.1
    (by simp [TopLevelCircuit.numInputs, squareTop, TopLevelCircuit.ofIndep, square,
      Offset.start])

-- the prover's public inputs are in the relation, and are `[x · x]`
example (hint : ProverHint F) (x : F) :
    (squareTop (F := F)).Relation
      ((((squareTop (F := F)).formalCircuit.main (some x)).operations Offset.start).compute hint
        ([1], [])).1.tail ∧
    ((((squareTop (F := F)).formalCircuit.main (some x)).operations Offset.start).compute hint
        ([1], [])).1.tail = [x * x] :=
  ⟨squareTop.completeness hint x trivial, rfl⟩

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

def pairTop : TopLevelCircuit F (Bool × F) (Variable × (Variable × Variable)) :=
  .ofIndep (pair allocBit pub rfl rfl)
    (pair_indep allocBit pub rfl rfl ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
      ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩) rfl

-- the key's rows: the two children's rows, then one appended row for each of ONE and the value
example : ((pairTop (F := ZMod 7)).formalCircuit.rowsAt none Offset.start).length = 2 ∧
    (pairTop (F := ZMod 7)).numInputs = 2 ∧ (pairTop (F := ZMod 7)).keyRows.length = 4 := by
  decide

-- public inputs `[y]` in the relation: the bit (aux 0) is boolean, and `y` is the value (aux 1)
example (y : F) (h : (pairTop (F := F)).Relation [y]) :
    ∃ aux : ℕ → F, (aux 0 = 0 ∨ aux 0 = 1) ∧ y = aux 1 := by
  obtain ⟨aux, hb, hp⟩ := pairTop.soundness [y] h
  exact ⟨aux, hb, hp⟩

-- for every private bit and value, the prover's public inputs are in the relation, and are the
-- value
example (hint : ProverHint F) (b : Bool) (v : F) :
    (pairTop (F := F)).Relation
      ((((pairTop (F := F)).formalCircuit.main (some (b, v))).operations Offset.start).compute
        hint ([1], [])).1.tail ∧
    ((((pairTop (F := F)).formalCircuit.main (some (b, v))).operations Offset.start).compute
        hint ([1], [])).1.tail = [v] := by
  refine ⟨pairTop.completeness hint (b, v) ⟨trivial, trivial⟩, ?_⟩
  simp only [pairTop, TopLevelCircuit.ofIndep, pair, pairMain, circuit_norm,
    FormalCircuit.operations_call]
  rfl

/-! ## No public inputs -/

def bitTop : TopLevelCircuit F Bool Variable :=
  .ofIndep allocBit ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩ rfl

-- with no public input, the relation holds at `[]`, and only there
example : (bitTop (F := F)).Relation [] ∧ ∀ a : F, ¬ (bitTop (F := F)).Relation [a] := by
  refine ⟨bitTop.completeness (fun _ _ => #[]) true trivial, fun a h => ?_⟩
  exact absurd h.1
    (by simp [TopLevelCircuit.numInputs, bitTop, TopLevelCircuit.ofIndep, allocBit, Offset.start])

end Bellman.Tests.TestTopLevel
