import Clean.Bellman.Semantics
import Mathlib.Data.Int.Notation
import Mathlib.Data.ZMod.Defs

/-!
Pins what a bellman constraint system means, mainly on `AllocatedBit::alloc` (`boolean.rs:70-99`):

- `circuit_norm` evaluates the linear combinations gadget code writes, and turns the bit's
  constraint into the equation bellman checks, `(ONE − a) · a = 0`;
- it evaluates whole linear combinations added in, scaled or not: `Boolean::enforce_equal`'s
  row on two allocated bits is the equation `a = b`; `Num::lc` scales a number's value, and
  `Num::add_bool_with_coeff` adds a scaled bit;
- with ONE = 1 that forces `a` to be a bit (soundness), and an honest assignment whose
  witness value is a bit satisfies it (completeness);
- `ExtendsWitnesses` asks exactly that the allocated variable holds its witness value;
- namespaces change neither predicate; `Constraints` matches the rows read off the operations;
- `ExtendsWitnesses` is a fixed-point condition: a witness function reading a later variable
  still satisfies it;
- `Constraints` is decidable: the kernel checks a concrete row over the BLS12-381 scalar field.
-/

namespace Bellman.Tests.TestSemantics
open Bellman

/-- The bit's witness function: it reads the prover's hint (any function would do here). -/
def w : ProverEnvironment ℤ → ℤ := fun env => (env.hint "bit" 1).getD 0 #v[0] |>.get 0

def allocBit : Circuit ℤ Variable := do
  let a ← alloc "boolean" w
  enforce "boolean constraint" (· + one - a) (· + a) (·)
  pure a

-- the value of `ONE − a`
example (env : Environment ℤ) :
    ((LinearCombination.zero : LinearCombination ℤ) + one - (⟨.aux 0⟩ : Variable)).eval env
      = env.input 0 - env.aux 0 := by
  simp only [circuit_norm]

-- scaled terms, as gadget code writes them (`lc + (c, v)`, `lc - (c, v)`)
example (env : Environment ℤ) :
    ((LinearCombination.zero : LinearCombination ℤ) + ((3 : ℤ), (⟨.aux 0⟩ : Variable))
        - ((2 : ℤ), (⟨.aux 1⟩ : Variable))).eval env
      = 3 * env.aux 0 - 2 * env.aux 1 := by
  simp only [circuit_norm]

-- whole linear combinations, scaled or not (`lc + &other`, `lc + (c, &other)`, `-` forms)
example (env : Environment ℤ) (lc other : LinearCombination ℤ) (c : ℤ) :
    (lc + other).eval env = lc.eval env + other.eval env ∧
      (lc - other).eval env = lc.eval env - other.eval env ∧
      (lc + (c, other)).eval env = lc.eval env + c * other.eval env ∧
      (lc - (c, other)).eval env = lc.eval env - c * other.eval env := by
  simp only [circuit_norm, and_self]

-- `Boolean::enforce_equal` on two allocated bits (`boolean.rs:375-419`): its row is
-- `0 · 0 = a.lc(one, 1) - &b.lc(one, 1)`, where an allocated bit's `Boolean::lc(one, c)` is
-- `zero + (c, v)` (`boolean.rs:429-447`); it is the equation `a = b`
example (env : Environment ℤ) (a b : Variable) :
    (⟨LinearCombination.zero, LinearCombination.zero,
      (LinearCombination.zero : LinearCombination ℤ) + ((1 : ℤ), a)
        - ((LinearCombination.zero : LinearCombination ℤ) + ((1 : ℤ), b))⟩
      : Constraint ℤ).Holds env ↔ env.get a = env.get b := by
  simp only [circuit_norm, mul_zero, one_mul, zero_add]
  rw [eq_comm, sub_eq_zero]

-- `Num::lc(coeff)`, `zero + (coeff, &self.lc)`, scales the number's value, and
-- `Num::add_bool_with_coeff` adds `coeff` times the bit (`num.rs:394-414`)
example (env : Environment ℤ) (num : LinearCombination ℤ) (c : ℤ) (v : Variable) :
    ((LinearCombination.zero : LinearCombination ℤ) + (c, num)).eval env = c * num.eval env ∧
      (num + ((LinearCombination.zero : LinearCombination ℤ) + (c, v))).eval env
        = num.eval env + c * env.get v := by
  simp only [circuit_norm, zero_add, and_self]

-- the bit's constraint is the equation bellman checks
example (env : Environment ℤ) :
    Constraints env allocBit.operations ↔ (env.input 0 - env.aux 0) * env.aux 0 = 0 := by
  simp only [Circuit.operations, allocBit, bind, alloc, enforce, circuit_norm]

-- soundness: with ONE = 1, the constraint forces the bit to be 0 or 1
example (env : Environment ℤ) (h1 : env.input 0 = 1)
    (h : Constraints env allocBit.operations) : env.aux 0 = 0 ∨ env.aux 0 = 1 := by
  simp only [Circuit.operations, allocBit, bind, alloc, enforce, circuit_norm, h1] at h
  rcases mul_eq_zero.mp h with h | h
  · right; linarith
  · left; exact h

-- the honest assignment: the allocated variable holds its witness value
example (env : ProverEnvironment ℤ) :
    ExtendsWitnesses env allocBit.operations Offset.start ↔ env.aux 0 = w env := by
  simp only [Circuit.operations, allocBit, bind, alloc, enforce, circuit_norm, and_true]

-- completeness: an honest assignment whose witness value is a bit satisfies the constraint
example (env : ProverEnvironment ℤ) (h1 : env.input 0 = 1)
    (hw : ExtendsWitnesses env allocBit.operations Offset.start) (hbit : w env = 0 ∨ w env = 1) :
    Constraints (env : Environment ℤ) allocBit.operations := by
  simp only [Circuit.operations, allocBit, bind, alloc, enforce, circuit_norm, and_true] at hw
  simp only [Circuit.operations, allocBit, bind, alloc, enforce, circuit_norm, h1, hw]
  rcases hbit with h | h <;> simp [h]

-- namespaces change neither predicate
def nested : Circuit ℤ Variable := withNamespace "outer" (withNamespace "inner" allocBit)

example (env : Environment ℤ) :
    Constraints env nested.operations ↔ Constraints env allocBit.operations := by
  simp only [Circuit.operations, nested, withNamespace, allocBit, bind, alloc, enforce,
    List.cons_append, List.nil_append, circuit_norm, true_and, and_true]

example (env : ProverEnvironment ℤ) :
    ExtendsWitnesses env nested.operations Offset.start
      ↔ ExtendsWitnesses env allocBit.operations Offset.start := by
  simp only [Circuit.operations, nested, withNamespace, allocBit, bind, alloc, enforce,
    List.cons_append, List.nil_append, circuit_norm, true_and, and_true]

-- `Constraints` matches the rows read off the operations
def twoBits : Circuit ℤ (Variable × Variable) := do
  let a ← withNamespace "first" allocBit
  let b ← withNamespace "second" allocBit
  pure (a, b)

example (env : Environment ℤ) :
    Constraints env twoBits.operations ↔ ∀ r ∈ twoBits.operations.constraints, r.Holds env :=
  constraints_iff_forall_mem env _

-- a fixed-point condition: `a` reads `b`, allocated after it, and is still satisfiable
def readsLater : Circuit ℤ Unit := do
  let _a ← alloc "a" fun env => env.aux 1
  let _b ← alloc "b" fun _ => 7
  pure ()

example : ∃ env : ProverEnvironment ℤ,
    ExtendsWitnesses env readsLater.operations Offset.start :=
  ⟨⟨⟨fun _ => 0, fun _ => 7⟩, default⟩, by
    simp only [Circuit.operations, readsLater, bind, alloc, circuit_norm, and_true]⟩

-- decidable: the kernel checks the bit row over the BLS12-381 scalar field, both ways
abbrev q : ℕ := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

def bitOps : Operations (ZMod q) := Circuit.operations (do
  let a ← alloc "boolean" fun _ => 1
  enforce "boolean constraint" (· + one - a) (· + a) (·)
  pure a)

example : Constraints (⟨fun i => if i = 0 then 1 else 0, fun _ => 1⟩ : Environment (ZMod q))
    bitOps := by decide
example : ¬ Constraints (⟨fun i => if i = 0 then 1 else 0, fun _ => 2⟩ : Environment (ZMod q))
    bitOps := by decide

end Bellman.Tests.TestSemantics
