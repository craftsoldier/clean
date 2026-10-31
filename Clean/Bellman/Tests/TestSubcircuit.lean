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
  spec, in soundness and in completeness.
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
    intro o env v _ _ h
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, circuit_norm] at h ⊢
    exact h.symm

/-- Call `b` twice in sequence, given that `b` raises to the power `k` and assumes nothing. -/
def twice (b : FormalCircuit F Variable Variable) (k : ℕ)
    (hb : ∀ env v c, b.Spec env v c → env.get c = env.get v ^ k)
    (hA : ∀ env v, b.Assumptions env v) :
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
  completeness o env v h1 _ h := by
    simp only [circuit_norm] at h
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact b.completeness_call o env v h1 (hA _ _) h.1 r hr
    · exact b.completeness_call _ env _ h1 (hA _ _) h.2 r hr

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
      ∀ env v, b.Assumptions env v }
  | 0 => ⟨square, fun _ _ _ h => by rw [ex_zero]; exact h, fun _ _ => trivial⟩
  | d + 1 => ⟨twice (nest d).1 _ (nest d).2.1 (nest d).2.2,
      fun env v c h => by rw [ex_succ]; exact h, fun _ _ => trivial⟩

-- soundness of 1,024 gadgets through the children's specs
example (o : Offset) (env : Environment F) (v : Variable) (h1 : env.input 0 = 1)
    (h : ∀ r ∈ (((nest (F := F) 10).1.call v).operations o).constraints, r.Holds env) :
    env.get (((nest (F := F) 10).1.call v).output o) = env.get v ^ ex 10 := by
  rw [FormalCircuit.constraints_call] at h
  rw [FormalCircuit.output_call]
  exact (nest 10).2.1 _ _ _ ((nest 10).1.soundness o env v h1 ((nest 10).2.2 _ _) h)

-- the assignment computed from ONE satisfies every row of the 1,024 gadgets
example (hint : ProverHint F) (v : Variable) (hv : v.Below Offset.start) :
    ∀ r ∈ (nest (F := F) 10).1.rowsAt v Offset.start,
      r.Holds ((nest (F := F) 10).1.computedEnv hint v Offset.start [1] []).toEnvironment :=
  (nest 10).1.complete_computed hint v _ [1] [] rfl rfl rfl hv ((nest 10).2.2 _ _)

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
    intro o env v h1 _ h
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, circuit_norm, h1] at h ⊢
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
    rintro o env ⟨a, b, cond⟩ _ hb h
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
    intro o env x h1 _ h
    simp only [reverseByBitMain, circuit_norm, List.cons_append, List.nil_append] at h
    obtain ⟨hbit, -, hrev⟩ := h
    have rb := allocBit.completeness_call o env _ h1 trivial hbit
    have sb := allocBit.soundness o env.toEnvironment _ h1 trivial rb
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact rb r hr
    · exact condReverse.completeness_call _ env _ h1 sb hrev r hr

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
  refine ⟨reverseByBit.complete_computed _ _ _ [1, 3] [] rfl rfl rfl
    ⟨show 1 < 2 by omega, trivial⟩ trivial, ?_⟩
  simp only [envS, FormalCircuit.computedEnv, reverseByBit, reverseByBitMain, circuit_norm,
    FormalCircuit.operations_call, FormalCircuit.output_call, FormalCircuit.nextOffset_call]
  decide

end Bellman.Tests.TestSubcircuit
