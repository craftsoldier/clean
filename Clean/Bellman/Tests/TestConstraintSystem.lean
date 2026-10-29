import Clean.Bellman.Basic
import Mathlib.Data.Int.Notation

/-!
Pins what running a bellman circuit produces, against bellman 0.15.0:

- inputs and auxiliary variables are numbered independently, from `Offset.start` (ONE is
  input 0; `TestConstraintSystem::alloc`/`alloc_input`, `test/mod.rs:363-391`);
- `enforce` builds each linear combination from the empty one: `AllocatedBit::alloc`'s row
  is `(ONE − a) · a = 0` exactly as bellman emits it (`boolean.rs:70-99`);
- namespaces change no variable, offset or constraint;
- constraints come out in program order, across namespaces.
-/

namespace Bellman.Tests.TestConstraintSystem
open Bellman

/-- A witness function that is never run here: emitting operations ignores it. -/
def w : ProverEnvironment ℤ → ℤ := fun _ => 0

-- inputs and auxiliary variables are numbered independently
def threeAllocs : Circuit ℤ (Variable × Variable × Variable) := do
  let a ← alloc "a" w
  let x ← allocInput "x" w
  let b ← alloc "b" w
  pure (a, x, b)

example : threeAllocs.output = (⟨.aux 0⟩, ⟨.input 1⟩, ⟨.aux 1⟩) := rfl
example : threeAllocs.nextOffset = ⟨2, 2⟩ := rfl
example : threeAllocs.operations.constraints = [] := rfl

-- `AllocatedBit::alloc`: allocate `a`, enforce `(ONE − a) · a = 0`
def allocBit : Circuit ℤ Variable := do
  let a ← alloc "boolean" w
  enforce "boolean constraint" (· + one - a) (· + a) (·)
  pure a

def bitRow (j : ℕ) : Constraint ℤ :=
  ⟨⟨[(one, 1), (⟨.aux j⟩, -1)]⟩, ⟨[(⟨.aux j⟩, 1)]⟩, ⟨[]⟩⟩

example : allocBit.operations.constraints = [bitRow 0] := rfl
-- the same circuit from any offset allocates the next auxiliary variable
example : (allocBit.operations ⟨5, 7⟩).constraints = [bitRow 7] := rfl
example : allocBit.nextOffset ⟨5, 7⟩ = ⟨5, 8⟩ := rfl

-- namespaces change no variable, offset or constraint
def nested : Circuit ℤ Variable := withNamespace "outer" (withNamespace "inner" allocBit)

example : nested.output = allocBit.output := rfl
example : nested.nextOffset = allocBit.nextOffset := rfl
example : nested.operations.constraints = allocBit.operations.constraints := rfl

-- constraints come out in program order, across namespaces
def twoBits : Circuit ℤ (Variable × Variable) := do
  let a ← withNamespace "first" allocBit
  let b ← withNamespace "second" allocBit
  pure (a, b)

example : twoBits.output = (⟨.aux 0⟩, ⟨.aux 1⟩) := rfl
example : twoBits.operations.constraints = [bitRow 0, bitRow 1] := rfl

end Bellman.Tests.TestConstraintSystem
