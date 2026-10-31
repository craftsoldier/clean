import Clean.Bellman.Formal
import Mathlib.Data.Int.Notation
import Mathlib.Data.ZMod.Defs

/-!
Pins the gadget bundle on bellman 0.15.0 gadgets ported as bundles, over a field and over
`ZMod 7`:

- `AllocatedNum::mul`: soundness reads the product; the assignment its witness functions
  compute satisfies its row (`complete_computed`), and its output is the product;
- the emission lemma: after any circuit, a gadget's rows follow that circuit's rows, at the
  offset it leaves;
- a witness function reading the variable it allocates is not computable; one reading ONE
  is, at any offset past it;
- `AllocatedBit::alloc` over a captured `Option` value: its rows do not depend on the value;
- `AllocatedNum::assert_nonzero`: complete only under its assumption; at zero the computed
  assignment violates the row;
- `AllocatedNum::conditionally_reverse`: sound only under its assumption (a boolean
  condition); with condition 2 the rows hold and neither order results;
- `AllocatedNum::alloc` then `inputize`, from the whole circuit's start: the computed public
  input is the value, and the row forces it.
-/

namespace Bellman.Tests.TestFormal
open Bellman

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable {F : Type} [Field F]

/-! ## `AllocatedNum::mul` -/

/-- `AllocatedNum::mul` (`num.rs:221-251`), on the variables of its two operands. -/
def mulMain (ab : Variable × Variable) : Circuit F Variable := do
  let c ← alloc "product num"
    (fun env => env.toEnvironment.get ab.1 * env.toEnvironment.get ab.2)
  enforce "multiplication constraint" (· + ab.1) (· + ab.2) (· + c)
  pure c

def mul : FormalCircuit F (Variable × Variable) Variable where
  main := mulMain
  rowsAt ab o := [⟨(LinearCombination.zero : LinearCombination F) + ab.1,
    (LinearCombination.zero : LinearCombination F) + ab.2,
    (LinearCombination.zero : LinearCombination F) + (⟨.aux o.aux⟩ : Variable)⟩]
  output _ o := ⟨.aux o.aux⟩
  nextOffset _ o := { o with aux := o.aux + 1 }
  computable ab o _ h := ⟨fun e e' he => by
    simp only [Variable.get_agrees h.1 he, Variable.get_agrees h.2 he], trivial⟩
  output_below _ o _ := by show o.aux < o.aux + 1; omega
  Spec env ab c := env.get c = env.get ab.1 * env.get ab.2
  soundness := by
    intro o env ab _ _ h
    simp only [List.mem_singleton, forall_eq, circuit_norm, zero_add] at h
    exact h.symm
  completeness := by
    intro o env ab _ _ hw
    simp only [mulMain, circuit_norm, List.append_nil, List.singleton_append] at hw
    simp only [List.mem_singleton, forall_eq, circuit_norm, zero_add]
    exact hw.symm

-- the assignment computed from inputs `[1, 3, 5]` satisfies the row, so its output is `3 · 5`
example : ((mul (F := ZMod 7)).computedEnv (fun _ _ => #[]) (⟨.input 1⟩, ⟨.input 2⟩)
    ⟨3, 0⟩ [1, 3, 5] []).aux 0 = 3 * 5 := by
  have hr := (mul (F := ZMod 7)).complete_computed (fun _ _ => #[]) (⟨.input 1⟩, ⟨.input 2⟩)
    ⟨3, 0⟩ [1, 3, 5] [] rfl rfl rfl ⟨show 1 < 3 by omega, show 2 < 3 by omega⟩ trivial
  exact mul.soundness ⟨3, 0⟩ _ (⟨.input 1⟩, ⟨.input 2⟩) (by decide) trivial hr

/-! ## The emission lemma -/

-- after an allocation, which emits no row
example (o : Offset) :
    ((alloc (F := F) "p" (fun _ => 0) >>= fun y => (mul (F := F)).main (y, y)).operations
      o).constraints
      = (mul (F := F)).rowsAt (⟨.aux o.aux⟩, ⟨.aux o.aux⟩) { o with aux := o.aux + 1 } := by
  rw [FormalCircuit.constraints_bind]; rfl

-- after a gadget with a row: that row comes first
example (o : Offset) (v : Variable) :
    (((mul (F := F)).main (v, v) >>= fun y => (mul (F := F)).main (y, v)).operations
      o).constraints
      = (mul (F := F)).rowsAt (v, v) o ++
        (mul (F := F)).rowsAt (⟨.aux o.aux⟩, v) { o with aux := o.aux + 1 } := by
  rw [FormalCircuit.constraints_bind, mul.rowsAt_eq]; rfl

/-! ## Reading only earlier variables -/

-- the product of the variable being allocated with itself: two environments agreeing before
-- the offset give different values
example : ¬ (((mul (F := ZMod 7)).main (⟨.aux 0⟩, ⟨.aux 0⟩)).operations
    ⟨1, 0⟩).ComputableWitnesses ⟨1, 0⟩ := by
  intro h
  have := h.1
    (ProverEnvironment.mk ⟨fun _ => 0, fun _ => 1⟩ (fun _ _ => #[]))
    (ProverEnvironment.mk ⟨fun _ => 0, fun _ => 2⟩ (fun _ _ => #[]))
    ⟨fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _), rfl⟩
  revert this; decide

-- a witness function reading ONE, at an offset past it
example (o : Offset) (ho : 0 < o.input) :
    ((alloc (F := F) "one" fun env => env.toEnvironment.get one).operations
      o).ComputableWitnesses o :=
  ⟨fun _ _ h => h.1 0 ho, trivial⟩

/-! ## `AllocatedBit::alloc` -/

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

-- its rows do not depend on the captured value: key generation, with `none`, emits the
-- prover's rows
example (v v' : Option Bool) (o : Offset) :
    (((allocBit (F := F)).main v).operations o).constraints =
      (((allocBit (F := F)).main v').operations o).constraints := rfl

/-! ## `AllocatedNum::assert_nonzero` -/

/-- `AllocatedNum::assert_nonzero` (`num.rs:284-312`). Rust's witness function fails at zero;
the Lean one returns `0⁻¹ = 0`, so completeness assumes a nonzero input. -/
def assertNonzero : FormalCircuit F Variable Unit where
  main v := do
    let inv ← alloc "ephemeral inverse" fun env => (env.get v)⁻¹
    enforce "nonzero assertion constraint" (· + v) (· + inv) (· + one)
  rowsAt v o := [⟨LinearCombination.zero + v,
    LinearCombination.zero + (⟨.aux o.aux⟩ : Variable), LinearCombination.zero + one⟩]
  output _ _ := ()
  nextOffset _ o := { o with aux := o.aux + 1 }
  computable v o _ hv := ⟨fun e e' h => by
    show (e.toEnvironment.get v)⁻¹ = (e'.toEnvironment.get v)⁻¹
    rw [Variable.get_agrees hv h], trivial⟩
  output_below _ _ _ := trivial
  Spec env v _ := env.get v ≠ 0
  Assumptions env v := env.get v ≠ 0
  soundness := by
    intro o env v h1 _ h
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, circuit_norm] at h ⊢
    intro hv
    rw [hv, h1] at h
    simp at h
  completeness := by
    intro o env v h1 hv h
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, circuit_norm] at h ⊢
    rw [h, h1]
    exact mul_inv_cancel₀ hv

-- at 0 the computed assignment violates the row
example : ¬ ∀ r ∈ (assertNonzero (F := ZMod 7)).rowsAt ⟨.input 1⟩ ⟨2, 0⟩,
    r.Holds ((assertNonzero (F := ZMod 7)).computedEnv (fun _ _ => #[]) ⟨.input 1⟩ ⟨2, 0⟩
      [1, 0] []).toEnvironment := by
  decide

-- at 3 the assumption holds, and the computed assignment satisfies the row
example : ∀ r ∈ (assertNonzero (F := ZMod 7)).rowsAt ⟨.input 1⟩ ⟨2, 0⟩,
    r.Holds ((assertNonzero (F := ZMod 7)).computedEnv (fun _ _ => #[]) ⟨.input 1⟩ ⟨2, 0⟩
      [1, 3] []).toEnvironment :=
  assertNonzero.complete_computed _ _ _ [1, 3] [] rfl rfl rfl (show 1 < 2 by omega)
    (show ((assertNonzero (F := ZMod 7)).computedEnv (fun _ _ => #[]) ⟨.input 1⟩ ⟨2, 0⟩
      [1, 3] []).toEnvironment.get ⟨.input 1⟩ ≠ 0 by decide)

/-! ## `AllocatedNum::conditionally_reverse` -/

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

/-- ONE, `a = 3`, `b = 5`, condition `2`; the two outputs `0` and `1`. -/
def envR : Environment (ZMod 7) :=
  ⟨fun i => [1, 3, 5, 2][i]?.getD 0, fun j => [0, 1][j]?.getD 0⟩

-- with condition 2 the rows hold, and the first output is neither input: the assumption is
-- needed
example :
    (∀ r ∈ (condReverse (F := ZMod 7)).rowsAt (⟨.input 1⟩, ⟨.input 2⟩, ⟨.input 3⟩)
      ⟨4, 0⟩, r.Holds envR) ∧
      envR.aux 0 ≠ envR.input 1 ∧ envR.aux 0 ≠ envR.input 2 := by
  decide

/-! ## `AllocatedNum::alloc` and `inputize` -/

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
    intro o env _ h1 _ hw
    simp only [pubMain, circuit_norm, List.append_nil, List.cons_append,
      List.nil_append] at hw
    simp only [List.mem_singleton, forall_eq, circuit_norm, zero_add, h1, mul_one]
    exact hw.2

-- from the whole circuit's start, the computed public input is the value
example : ((pub (F := ZMod 7)).computedEnv (fun _ _ => #[]) (some 4) Offset.start [1] []).input 1
    = 4 := by
  have hr := (pub (F := ZMod 7)).complete_computed (fun _ _ => #[]) (some 4) Offset.start [1] []
    rfl rfl rfl trivial trivial
  have := pub.soundness Offset.start _ (some 4) (by decide) trivial hr
  have h0 : ((pub (F := ZMod 7)).computedEnv (fun _ _ => #[]) (some 4) Offset.start [1]
    []).aux 0 = 4 := by decide
  exact this.trans h0

-- and the row forces it: an input different from the value violates the row
example : ¬ ∀ r ∈ (pub (F := ZMod 7)).rowsAt none Offset.start,
    r.Holds (⟨fun i => [1, 2][i]?.getD 0, fun _ => 3⟩ : Environment (ZMod 7)) := by
  decide

end Bellman.Tests.TestFormal
