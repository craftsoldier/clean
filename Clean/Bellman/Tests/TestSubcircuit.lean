import Clean.Bellman.Subcircuit
import Mathlib.Data.ZMod.Defs

/-!
Pins calls on parents built from bundles, each proved through its children's bundles only:

- `twice` calls a child twice; a tree of `2 ^ 10` squaring gadgets is sound through the
  children's specs, and the assignment computed from ONE satisfies all its rows;
- the rows are emitted inline: at depth 2, with every call opened (`operations_call`), the
  circuit's own rows are the four squarings;
- `reverseByBit`, a parent bundle built from its children's bundles and one allocation: a bit
  (`AllocatedBit::alloc`), a value, and `AllocatedNum::conditionally_reverse` by the bit, each in
  its namespace; the reversal's assumption, a boolean condition, comes from the bit gadget's
  spec, in soundness and in completeness;
- `andBits`, two allocated bits ANDed (`AllocatedBit::and`) through calls: its prover's output is
  the AND of the captured bits, read from the bits' prover-side specs without opening their
  operations. The AND is sound on any inputs and takes them being bits as a prover-side
  assumption, which the bits' prover-side specs supply.
-/

namespace Bellman.Tests.TestSubcircuit
open Bellman

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable {F : Type} [Field F]

/-- `AllocatedNum::square` (`num.rs:253-282`). -/
def square : FormalCircuit F Variable Variable where
  main v := do
    let c ← alloc "squared num" fun env => env.get v * env.get v
    enforce "squaring constraint" (· + v) (· + v) (· + c)
    pure c
  rowsAt v o := [⟨LinearCombination.zero + v, LinearCombination.zero + v,
    LinearCombination.zero + (⟨.aux o.aux⟩ : Variable)⟩]
  output _ o := ⟨.aux o.aux⟩
  nextOffset _ o := { o with aux := o.aux + 1 }
  computable v o _ hv :=
    ⟨fun e e' h => by
      have hg := Variable.get_agrees hv h
      exact congrArg₂ (· * ·) hg hg, trivial⟩
  output_below _ o _ := by show o.aux < o.aux + 1; omega
  Spec env v c := env.get c = env.get v ^ 2
  soundness := by
    intro o env v _ _ h
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, circuit_norm] at h ⊢
    rw [← h, sq]
  completeness := by
    intro o env v _ _ _ h
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, circuit_norm] at h ⊢
    exact h.symm

/-- Call `b` twice in sequence, given that `b` raises to the power `k` and has no assumptions and
no prover-side assumptions. -/
def twice (b : FormalCircuit F Variable Variable) (k : ℕ)
    (hb : ∀ env v c, b.Spec env v c → env.get c = env.get v ^ k)
    (hA : ∀ env v, b.Assumptions env v) (hP : ∀ env v, b.ProverAssumptions env v) :
    FormalCircuit F Variable Variable where
  main v := do
    let a ← b.call v
    b.call a
  rowsAt v o := b.rowsAt v o ++ b.rowsAt (b.output v o) (b.nextOffset v o)
  rowsAt_eq v o := by simp only [circuit_norm]
  output v o := b.output (b.output v o) (b.nextOffset v o)
  output_eq v o := by simp only [circuit_norm]
  nextOffset v o := b.nextOffset (b.output v o) (b.nextOffset v o)
  nextOffset_eq v o := by simp only [circuit_norm]
  advance_eq v o := by simp only [circuit_norm]
  computable v o ho hv := by
    simp only [circuit_norm]
    -- offsets only grow, so the second call also starts past ONE
    exact ⟨b.computable_call v o ho hv, b.computable_call _ _
      (Nat.lt_of_lt_of_le ho (b.le_nextOffset v o).1) (b.output_below v o hv)⟩
  output_below v o hv := b.output_below _ _ (b.output_below v o hv)
  Spec env v c := env.get c = env.get v ^ (k * k)
  soundness o env v h1 _ h := by
    have h₁ := hb _ _ _ (b.soundness o env v h1 (hA _ _)
      fun r hr => h r (List.mem_append_left _ hr))
    have h₂ := hb _ _ _ (b.soundness _ env _ h1 (hA _ _)
      fun r hr => h r (List.mem_append_right _ hr))
    rw [h₂, h₁, ← pow_mul]
  completeness o env v h1 _ _ h := by
    simp only [circuit_norm] at h
    refine ⟨fun r hr => ?_, trivial⟩
    rcases List.mem_append.1 hr with hr | hr
    · exact (b.completeness_call o env v h1 (hA _ _) (hP _ _) h.1).1 r hr
    · exact (b.completeness_call _ env _ h1 (hA _ _) (hP _ _) h.2).1 r hr

/-- The exponent after `d` doublings of the tree, `2 ^ 2 ^ d`, kept folded so that Lean does
not evaluate it. -/
def ex : ℕ → ℕ
  | 0 => 2
  | d + 1 => ex d * ex d

theorem ex_zero : ex 0 = 2 := rfl
theorem ex_succ (d : ℕ) : ex (d + 1) = ex d * ex d := rfl
attribute [irreducible] ex

/-- `2 ^ d` squaring gadgets, each level calling the one below twice. -/
def nest : (d : ℕ) → { b : FormalCircuit F Variable Variable //
    (∀ env v c, b.Spec env v c → env.get c = env.get v ^ ex d) ∧
      (∀ env v, b.Assumptions env v) ∧ ∀ env v, b.ProverAssumptions env v }
  | 0 => ⟨square, fun _ _ _ h => by rw [ex_zero]; exact h, fun _ _ => trivial,
      fun _ _ => trivial⟩
  | d + 1 => ⟨twice (nest d).1 _ (nest d).2.1 (nest d).2.2.1 (nest d).2.2.2,
      fun env v c h => by rw [ex_succ]; exact h, fun _ _ => trivial, fun _ _ => trivial⟩

-- soundness of 1,024 gadgets through the children's specs
example (o : Offset) (env : Environment F) (v : Variable) (h1 : env.input 0 = 1)
    (h : ∀ r ∈ (((nest (F := F) 10).1.call v).operations o).constraints, r.Holds env) :
    env.get (((nest (F := F) 10).1.call v).output o) = env.get v ^ ex 10 := by
  rw [FormalCircuit.constraints_call] at h
  rw [FormalCircuit.output_call]
  exact (nest 10).2.1 _ _ _ ((nest 10).1.soundness o env v h1 ((nest 10).2.2.1 _ _) h)

-- the assignment computed from ONE satisfies every row of the 1,024 gadgets
example (hint : ProverHint F) (v : Variable) (hv : v.Below Offset.start) :
    ∀ r ∈ (nest (F := F) 10).1.rowsAt v Offset.start,
      r.Holds ((nest (F := F) 10).1.computedEnv hint v Offset.start [1] []).toEnvironment :=
  ((nest 10).1.complete_computed hint v _ [1] [] rfl rfl rfl hv ((nest 10).2.2.1 _ _)
    ((nest 10).2.2.2 _ _)).1

/-- The squaring row `a · a = c`. -/
def sqRow (a c : Variable) : Constraint (ZMod 7) :=
  ⟨(LinearCombination.zero : LinearCombination (ZMod 7)) + a,
    (LinearCombination.zero : LinearCombination (ZMod 7)) + a,
    (LinearCombination.zero : LinearCombination (ZMod 7)) + c⟩

-- the rows are emitted inline, as bellman does: depth 2's rows are 4 squarings, from
-- input 1, in the closed form and in the circuit's own operations, read by opening every call
-- (the kernel does not reduce through one)
example : (nest (F := ZMod 7) 2).1.rowsAt ⟨.input 1⟩ ⟨2, 0⟩ =
    [sqRow ⟨.input 1⟩ ⟨.aux 0⟩, sqRow ⟨.aux 0⟩ ⟨.aux 1⟩,
      sqRow ⟨.aux 1⟩ ⟨.aux 2⟩, sqRow ⟨.aux 2⟩ ⟨.aux 3⟩] := by
  decide
example : (((nest (F := ZMod 7) 2).1.main ⟨.input 1⟩).operations ⟨2, 0⟩).constraints =
    [sqRow ⟨.input 1⟩ ⟨.aux 0⟩, sqRow ⟨.aux 0⟩ ⟨.aux 1⟩,
      sqRow ⟨.aux 1⟩ ⟨.aux 2⟩, sqRow ⟨.aux 2⟩ ⟨.aux 3⟩] := by
  simp only [nest, twice, square, Circuit.operations_bind, FormalCircuit.operations_call,
    FormalCircuit.output_call, FormalCircuit.nextOffset_call]
  decide

/-! ## A parent bundle -/

/-- `AllocatedBit::alloc` (`boolean.rs:70-99`): the value is captured, `none` at key
generation. The prover assigns 1 or 0 as it is `true` or not. -/
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
  ProverSpec env v a := env.toEnvironment.get a = if v.getD false then 1 else 0
  soundness := by
    intro o env v h1 _ h
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, circuit_norm, h1] at h ⊢
    rcases mul_eq_zero.1 h with h | h
    · right; exact (sub_eq_zero.1 h).symm
    · left; exact h
  completeness := by
    intro o env v h1 _ _ h
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, circuit_norm, h1] at h ⊢
    refine ⟨?_, h⟩
    rw [h]; split <;> simp

/-- `AllocatedNum::conditionally_reverse` (`num.rs:317-357`), for a condition that is an
allocated bit (`Boolean::Is`). Its rows do not constrain the condition to be a bit, so soundness
assumes it. -/
def condReverse [DecidableEq F] :
    FormalCircuit F (Variable × Variable × Variable) (Variable × Variable) where
  main x := do
    let a := x.1; let b := x.2.1; let cond := x.2.2
    let c ← withNamespace "conditional reversal result 1" <|
      alloc "num" fun env => if env.get cond = 1 then env.get b else env.get a
    enforce "first conditional reversal" (· + a - b)
      (fun _ => (LinearCombination.zero : LinearCombination F) + ((1 : F), cond)) (· + a - c)
    let d ← withNamespace "conditional reversal result 2" <|
      alloc "num" fun env => if env.get cond = 1 then env.get a else env.get b
    enforce "second conditional reversal" (· + b - a)
      (fun _ => (LinearCombination.zero : LinearCombination F) + ((1 : F), cond)) (· + b - d)
    pure (c, d)
  rowsAt x o :=
    [⟨LinearCombination.zero + x.1 - x.2.1,
      (LinearCombination.zero : LinearCombination F) + ((1 : F), x.2.2),
      LinearCombination.zero + x.1 - (⟨.aux o.aux⟩ : Variable)⟩,
     ⟨LinearCombination.zero + x.2.1 - x.1,
      (LinearCombination.zero : LinearCombination F) + ((1 : F), x.2.2),
      LinearCombination.zero + x.2.1 - (⟨.aux (o.aux + 1)⟩ : Variable)⟩]
  output _ o := (⟨.aux o.aux⟩, ⟨.aux (o.aux + 1)⟩)
  nextOffset _ o := { o with aux := o.aux + 2 }
  computable x o _ hx := by
    obtain ⟨ha, hb, hc⟩ := hx
    refine ⟨fun e e' h => ?_, fun e e' h => ?_, trivial⟩
    · show (if e.toEnvironment.get _ = 1 then _ else _) =
        (if e'.toEnvironment.get _ = 1 then _ else _)
      rw [Variable.get_agrees hc h, Variable.get_agrees ha h, Variable.get_agrees hb h]
    · show (if e.toEnvironment.get _ = 1 then _ else _) =
        (if e'.toEnvironment.get _ = 1 then _ else _)
      have m := fun {v : Variable} (hv : v.Below o) =>
        Variable.get_agrees (o := { o with aux := o.aux + 1 }) (hv.mono le_rfl (Nat.le_succ _)) h
      rw [m hc, m ha, m hb]
  output_below _ o _ := by
    show o.aux < o.aux + 2 ∧ o.aux + 1 < o.aux + 2; omega
  Assumptions env x := env.get x.2.2 = 0 ∨ env.get x.2.2 = 1
  Spec env x y :=
    env.get y.1 = (if env.get x.2.2 = 1 then env.get x.2.1 else env.get x.1) ∧
    env.get y.2 = (if env.get x.2.2 = 1 then env.get x.1 else env.get x.2.1)
  soundness := by
    rintro o env ⟨a, b, cond⟩ _ hA h
    change env.get cond = 0 ∨ env.get cond = 1 at hA
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      circuit_norm] at h ⊢
    obtain ⟨h₁, h₂⟩ := h
    rcases hA with h0 | h1
    · simp only [h0, zero_ne_one, if_false, mul_zero] at h₁ h₂ ⊢
      exact ⟨(sub_eq_zero.1 h₁.symm).symm, (sub_eq_zero.1 h₂.symm).symm⟩
    · simp only [h1, if_true, mul_one, sub_right_inj] at h₁ h₂ ⊢
      exact ⟨h₁.symm, h₂.symm⟩
  completeness := by
    rintro o env ⟨a, b, cond⟩ _ hb _ h
    change env.get cond = 0 ∨ env.get cond = 1 at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      circuit_norm, List.cons_append, List.nil_append] at h ⊢
    obtain ⟨hc, hd⟩ := h
    rcases hb with h0 | h1
    · simp only [h0, zero_ne_one, if_false] at hc hd
      simp [hc, hd, h0]
    · simp only [h1, if_true] at hc hd
      simp [hc, hd, h1]

/-- A bit, a value, then the reversal of (cur, value) by the bit, each in its namespace: the
reversal's assumption, a boolean condition, comes from the bit gadget's spec. -/
def reverseByBitMain [DecidableEq F] (x : Variable × Option (F × Bool)) :
    Circuit F (Variable × Variable × Variable × Variable) := do
  let b ← withNamespace "bit" (allocBit.call (x.2.map (·.2)))
  let v ← withNamespace "value" (alloc "num" fun _ => (x.2.map (·.1)).getD 0)
  let r ← withNamespace "conditional reversal" (condReverse.call (x.1, v, b))
  pure (r.1, r.2, b, v)

-- `reverseByBit`'s closed-form fields name the reversal's offset and input four times; these
-- two definitions are those closed forms, written once
/-- The offset after the bit and the value. -/
def reverseByBitAt (x : Variable × Option (F × Bool)) (o : Offset) : Offset :=
  let o₁ := (allocBit (F := F)).nextOffset (x.2.map (·.2)) o
  { o₁ with aux := o₁.aux + 1 }

/-- The reversal's input: cur, the value, the bit. -/
def reverseByBitIn (x : Variable × Option (F × Bool)) (o : Offset) :
    Variable × Variable × Variable :=
  (x.1, ⟨.aux ((allocBit (F := F)).nextOffset (x.2.map (·.2)) o).aux⟩,
    (allocBit (F := F)).output (x.2.map (·.2)) o)

theorem reverseByBitIn_below (x : Variable × Option (F × Bool)) (o : Offset)
    (hx : HasBelow.Below x o) :
    HasBelow.Below (reverseByBitIn (F := F) x o) (reverseByBitAt (F := F) x o) := by
  have hle := (allocBit (F := F)).le_nextOffset (x.2.map (·.2)) o
  refine ⟨HasBelow.mono hx.1 hle.1 (Nat.le_succ_of_le hle.2), ?_,
    HasBelow.mono ((allocBit (F := F)).output_below _ o trivial) le_rfl (Nat.le_succ _)⟩
  show _ < _ + 1; omega

variable [DecidableEq F]

def reverseByBit :
    FormalCircuit F (Variable × Option (F × Bool)) (Variable × Variable × Variable × Variable)
    where
  main := reverseByBitMain
  rowsAt x o := allocBit.rowsAt (x.2.map (·.2)) o ++
    condReverse.rowsAt (reverseByBitIn x o) (reverseByBitAt x o)
  rowsAt_eq x o := by
    simp only [reverseByBitMain, circuit_norm, Operations.constraints, List.cons_append,
      List.nil_append]
    rfl
  output x o := ((condReverse.output (reverseByBitIn x o) (reverseByBitAt x o)).1,
    (condReverse.output (reverseByBitIn x o) (reverseByBitAt x o)).2,
    (reverseByBitIn x o).2.2, (reverseByBitIn x o).2.1)
  output_eq x o := by
    simp only [reverseByBitMain, circuit_norm]
    rfl
  nextOffset x o := condReverse.nextOffset (reverseByBitIn x o) (reverseByBitAt x o)
  nextOffset_eq x o := by
    simp only [reverseByBitMain, circuit_norm]
    rfl
  advance_eq x o := by
    simp only [reverseByBitMain, circuit_norm, Operations.advance, List.cons_append,
      List.nil_append]
    rfl
  computable x o ho hx := by
    simp only [reverseByBitMain, circuit_norm, Operations.ComputableWitnesses,
      List.cons_append, List.nil_append]
    -- the bit and the value allocate no input, so the reversal starts past ONE too
    exact ⟨allocBit.computable_call _ o ho trivial,
      condReverse.computable_call _ _ ho (reverseByBitIn_below x o hx)⟩
  output_below x o hx := by
    have hin := reverseByBitIn_below x o hx
    have hle := (condReverse (F := F)).le_nextOffset (reverseByBitIn x o) (reverseByBitAt x o)
    exact ⟨(condReverse.output_below _ _ hin).1, (condReverse.output_below _ _ hin).2,
      HasBelow.mono hin.2.2 hle.1 hle.2, HasBelow.mono hin.2.1 hle.1 hle.2⟩
  Spec env x y := (env.get y.2.2.1 = 0 ∨ env.get y.2.2.1 = 1) ∧
    condReverse.Spec env (x.1, y.2.2.2, y.2.2.1) (y.1, y.2.1)
  soundness := by
    intro o env x h1 _ h
    have hb := allocBit.soundness o env _ h1 trivial fun r hr => h r (List.mem_append_left _ hr)
    exact ⟨hb, condReverse.soundness _ env (reverseByBitIn x o) h1 hb
      fun r hr => h r (List.mem_append_right _ hr)⟩
  completeness := by
    intro o env x h1 _ _ h
    simp only [reverseByBitMain, circuit_norm, List.cons_append, List.nil_append] at h
    obtain ⟨hbit, -, hrev⟩ := h
    have rb := (allocBit.completeness_call o env _ h1 trivial trivial hbit).1
    have sb := allocBit.soundness o env.toEnvironment _ h1 trivial rb
    refine ⟨fun r hr => ?_, trivial⟩
    rcases List.mem_append.1 hr with hr | hr
    · exact rb r hr
    · exact (condReverse.completeness_call _ env _ h1 sb trivial hrev).1 r hr

-- the parent's spec, read: the bit is a bit and the pair is reversed by it
example (o : Offset) (env : Environment F) (x : Variable × Option (F × Bool))
    (h1 : env.input 0 = 1) (h : ∀ r ∈ (reverseByBit (F := F)).rowsAt x o, r.Holds env) :
    let y := (reverseByBit (F := F)).output x o
    env.get y.2.2.1 = 0 ∨ env.get y.2.2.1 = 1 :=
  (reverseByBit.soundness o env x h1 trivial h).1

/-- The computed assignment for `reverseByBit` from inputs `[1, 3]` (cur = input 1 = 3), with
value 5 and bit `true`. -/
def envS : ProverEnvironment (ZMod 7) :=
  (reverseByBit (F := ZMod 7)).computedEnv (fun _ _ => #[]) (⟨.input 1⟩, some (5, true))
    ⟨2, 0⟩ [1, 3] []

-- on it every row holds, and the outputs are reversed, (5, 3); evaluating it first opens the
-- calls with `operations_call`, since the kernel does not reduce through them
example : (∀ r ∈ (reverseByBit (F := ZMod 7)).rowsAt (⟨.input 1⟩, some (5, true))
      ⟨2, 0⟩, r.Holds envS.toEnvironment) ∧ envS.aux 2 = 5 ∧ envS.aux 3 = 3 := by
  refine ⟨(reverseByBit.complete_computed _ _ _ [1, 3] [] rfl rfl rfl
    ⟨show 1 < 2 by omega, trivial⟩ trivial trivial).1, ?_⟩
  simp only [envS, FormalCircuit.computedEnv, reverseByBit, reverseByBitMain, circuit_norm,
    FormalCircuit.operations_call, FormalCircuit.output_call, FormalCircuit.nextOffset_call]
  decide

/-! ## A parent reading its children's values -/

/-- `AllocatedBit::and` (`boolean.rs:155-190`): `a · b = c`. The prover assigns 1 when both
inputs are 1 and 0 otherwise, the product only on bits, so completeness assumes both are bits;
the row forces the product on any inputs. -/
def andBit : FormalCircuit F (Variable × Variable) Variable where
  main ab := do
    let c ← alloc "and result" fun env =>
      if env.toEnvironment.get ab.1 = 1 ∧ env.toEnvironment.get ab.2 = 1 then 1 else 0
    enforce "and constraint" (· + ab.1) (· + ab.2) (· + c)
    pure c
  rowsAt ab o := [⟨(LinearCombination.zero : LinearCombination F) + ab.1,
    (LinearCombination.zero : LinearCombination F) + ab.2,
    (LinearCombination.zero : LinearCombination F) + (⟨.aux o.aux⟩ : Variable)⟩]
  output _ o := ⟨.aux o.aux⟩
  nextOffset _ o := { o with aux := o.aux + 1 }
  computable ab o _ h := ⟨fun e e' he => by
    show (if _ then _ else _) = (if _ then _ else _)
    rw [Variable.get_agrees h.1 he, Variable.get_agrees h.2 he], trivial⟩
  output_below _ o _ := by show o.aux < o.aux + 1; omega
  Spec env ab c := env.get c = env.get ab.1 * env.get ab.2
  ProverAssumptions env ab :=
    (env.toEnvironment.get ab.1 = 0 ∨ env.toEnvironment.get ab.1 = 1) ∧
    (env.toEnvironment.get ab.2 = 0 ∨ env.toEnvironment.get ab.2 = 1)
  soundness := by
    intro o env ab _ _ h
    simp only [List.mem_singleton, forall_eq, circuit_norm, zero_add] at h ⊢
    exact h.symm
  completeness := by
    rintro o env ⟨a, b⟩ _ _ ⟨ha, hb⟩ hw
    simp only [circuit_norm, List.append_nil, List.singleton_append] at hw
    simp only [List.mem_singleton, forall_eq, circuit_norm, zero_add]
    rw [hw]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

/-- Two captured bits, allocated, then their AND, each through a call. -/
def andBitsMain (w : Option (Bool × Bool)) : Circuit F Variable := do
  let a ← allocBit.call (w.map Prod.fst)
  let b ← allocBit.call (w.map Prod.snd)
  andBit.call (a, b)

/-- The AND's input: the two bits. -/
def andBitsIn (w : Option (Bool × Bool)) (o : Offset) : Variable × Variable :=
  ((allocBit (F := F)).output (w.map Prod.fst) o,
    (allocBit (F := F)).output (w.map Prod.snd)
      ((allocBit (F := F)).nextOffset (w.map Prod.fst) o))

/-- The offset after the two bits. -/
def andBitsAt (w : Option (Bool × Bool)) (o : Offset) : Offset :=
  (allocBit (F := F)).nextOffset (w.map Prod.snd)
    ((allocBit (F := F)).nextOffset (w.map Prod.fst) o)

omit [DecidableEq F] in
theorem andBitsIn_below (w : Option (Bool × Bool)) (o : Offset) :
    HasBelow.Below (andBitsIn (F := F) w o) (andBitsAt (F := F) w o) := by
  have hle := (allocBit (F := F)).le_nextOffset (w.map Prod.snd)
    ((allocBit (F := F)).nextOffset (w.map Prod.fst) o)
  exact ⟨HasBelow.mono ((allocBit (F := F)).output_below _ o trivial) hle.1 hle.2,
    (allocBit (F := F)).output_below _ _ trivial⟩

/-- The AND of two captured bits: its rows force a bit, and its prover's value is the AND of the
captured values, read from the bits' prover-side specs. -/
def andBits : FormalCircuit F (Option (Bool × Bool)) Variable where
  main := andBitsMain
  rowsAt w o := allocBit.rowsAt (w.map Prod.fst) o ++
    allocBit.rowsAt (w.map Prod.snd) (allocBit.nextOffset (w.map Prod.fst) o) ++
    andBit.rowsAt (andBitsIn w o) (andBitsAt w o)
  rowsAt_eq w o := by simp only [andBitsMain, circuit_norm, List.append_assoc]; rfl
  output w o := andBit.output (andBitsIn w o) (andBitsAt w o)
  output_eq w o := by simp only [andBitsMain, circuit_norm]; rfl
  nextOffset w o := andBit.nextOffset (andBitsIn w o) (andBitsAt w o)
  nextOffset_eq w o := by simp only [andBitsMain, circuit_norm]; rfl
  advance_eq w o := by simp only [andBitsMain, circuit_norm]; rfl
  computable w o ho _ := by
    simp only [andBitsMain, circuit_norm]
    -- the bits allocate no input, so the AND starts past ONE too
    exact ⟨allocBit.computable_call _ o ho trivial, allocBit.computable_call _ _ ho trivial,
      andBit.computable_call _ _ ho (andBitsIn_below w o)⟩
  output_below w o _ := andBit.output_below _ _ (andBitsIn_below w o)
  Spec env _ c := env.get c = 0 ∨ env.get c = 1
  ProverSpec env w c := env.toEnvironment.get c =
    if (w.map Prod.fst).getD false && (w.map Prod.snd).getD false then 1 else 0
  soundness := by
    intro o env w h1 _ h
    simp only [List.mem_append] at h
    have ha := allocBit.soundness o env _ h1 trivial fun r hr => h r (.inl (.inl hr))
    have hb := allocBit.soundness _ env _ h1 trivial fun r hr => h r (.inl (.inr hr))
    have hc := andBit.soundness _ env (andBitsIn w o) h1 trivial fun r hr => h r (.inr hr)
    change env.get _ = env.get (andBitsIn w o).1 * env.get (andBitsIn w o).2 at hc
    rw [hc]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      simp only [andBitsIn] at ha hb ⊢ <;> simp [ha, hb]
  completeness := by
    intro o env w h1 _ _ h
    simp only [andBitsMain, circuit_norm] at h
    obtain ⟨ra, va⟩ := allocBit.completeness_call o env _ h1 trivial trivial h.1
    obtain ⟨rb, vb⟩ := allocBit.completeness_call _ env _ h1 trivial trivial h.2.1
    -- each bit's value is 0 or 1, as its prover-side spec gives it: the AND's prover-side
    -- assumption
    have bit : ∀ (t : Bool) (x : F), x = (if t then 1 else 0) → x = 0 ∨ x = 1 := by
      intro t x hx; cases t <;> simp [hx]
    -- the AND's offset is passed as `andBitsAt`, so that `hc` below names it as the output does
    obtain ⟨rc, -⟩ := andBit.completeness_call (andBitsAt w o) env (andBitsIn w o) h1 trivial
      ⟨bit _ _ va, bit _ _ vb⟩ h.2.2
    have hc := andBit.soundness (andBitsAt w o) env.toEnvironment (andBitsIn w o) h1 trivial rc
    refine ⟨fun r hr => ?_, ?_⟩
    · rcases List.mem_append.1 hr with hr | hr
      · rcases List.mem_append.1 hr with hr | hr
        · exact ra r hr
        · exact rb r hr
      · exact rc r hr
    · change env.toEnvironment.get _ =
        env.toEnvironment.get (andBitsIn w o).1 * env.toEnvironment.get (andBitsIn w o).2 at hc
      show env.toEnvironment.get (andBit.output (andBitsIn w o) (andBitsAt w o)) = _
      rw [hc]
      simp only [andBitsIn] at va vb ⊢
      rw [va, vb]
      cases (w.map Prod.fst).getD false <;> cases (w.map Prod.snd).getD false <;> simp

-- through a call, a bit's value is the captured one, from its prover-side spec
example (o : Offset) (env : ProverEnvironment F) (v : Option Bool) (h1 : env.input 0 = 1)
    (h : ExtendsWitnesses env (((allocBit (F := F)).call v).operations o) o) :
    env.toEnvironment.get ((allocBit (F := F)).output v o) = if v.getD false then 1 else 0 :=
  ((allocBit (F := F)).completeness_call o env v h1 trivial trivial h).2

-- on inputs 2 and 3, which are not bits, the assignment the AND's prover computes violates its
-- row: it assigns 0, and the row needs 6
example : ¬ ∀ r ∈ (andBit (F := ZMod 7)).rowsAt (⟨.input 1⟩, ⟨.input 2⟩) ⟨3, 0⟩,
    r.Holds ((andBit (F := ZMod 7)).computedEnv (fun _ _ => #[]) (⟨.input 1⟩, ⟨.input 2⟩)
      ⟨3, 0⟩ [1, 2, 3] []).toEnvironment := by
  decide

-- the assignment computed from ONE on `(true, true)` gives the parent's output 1
example : ((andBits (F := ZMod 7)).computedEnv (fun _ _ => #[]) (some (true, true)) ⟨1, 0⟩
    [1] []).toEnvironment.get ((andBits (F := ZMod 7)).output (some (true, true)) ⟨1, 0⟩) = 1 :=
  ((andBits (F := ZMod 7)).complete_computed (fun _ _ => #[]) (some (true, true)) ⟨1, 0⟩ [1] []
    rfl rfl rfl trivial trivial trivial).2

end Bellman.Tests.TestSubcircuit
