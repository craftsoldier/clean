import Clean.Bellman.LinearCombination
import Clean.Circuit.Expression

/-!
# bellman constraint-system operations

What a bellman 0.15.0 circuit does to its constraint system, as data: allocate a private or a
public variable, enforce a constraint `A · B = C`, and enter or leave a namespace. Running a
circuit (`Clean.Bellman.Basic`) produces the list of these operations in program order; the
constraint system's rows are the `enforce` constraints read off that list.

## Witness functions

An allocation carries the variable's witness function, which reads the prover's environment.
Emitting operations never runs a witness function, as groth16's key generation never runs
bellman's witness closures. A circuit can still take witness values as arguments, as bellman's
`Option` fields do; key generation passes `None`, so the prover's rows are the key's only when
they do not depend on those values. A bellman closure can fail (`AssignmentMissing`,
`DivisionByZero`); a witness function here is total, and a gadget whose closure can fail
excludes the failing case by a prover-side assumption instead.

## Namespaces

Namespaces only name things: they change no variable and no constraint. They are kept as flat
`pushNamespace`/`popNamespace` markers, as in bellman's root constraint-system API.

## Rust references (bellman 0.15.0, groth16 0.2.0)

- `src/lib.rs` — `ConstraintSystem` (`alloc`, `alloc_input`, `enforce`, `push_namespace`,
  `pop_namespace`)
- `src/gadgets/test/mod.rs` — `TestConstraintSystem` (variable numbering, ONE as input 0)
- groth16 `src/generator.rs`, `src/prover.rs` — the key generator's and the prover's
  constraint systems
-/

namespace Bellman

/-- Where a circuit's allocations start: the index of the next input and of the next
auxiliary variable. Inputs and auxiliary variables are numbered independently, each by its own
count (`TestConstraintSystem::alloc` and `alloc_input`, `test/mod.rs:363-391`). -/
structure Offset where
  input : ℕ
  aux : ℕ
deriving DecidableEq, Repr

/-- The offset a whole circuit starts at: ONE is already input `0`, and no auxiliary variable
is allocated. `TestConstraintSystem`, groth16 key generation and the groth16 prover all
allocate ONE before synthesis (`test/mod.rs:150-165`, `generator.rs:188`, `prover.rs:204`). -/
def Offset.start : Offset := ⟨1, 0⟩

variable {F : Type}

/-- An assignment of field elements to a constraint system's variables: inputs and auxiliary
variables, by index. -/
structure Environment (F : Type) where
  input : ℕ → F
  aux : ℕ → F

/-- What a witness function reads: the assignment, and the prover's hints (private data that
is not part of the constraint system). The hints are Clean's `ProverHint`. -/
structure ProverEnvironment (F : Type) extends Environment F where
  hint : ProverHint F

/-- A constraint `A · B = C` on linear combinations `A`, `B`, `C`: bellman's rows. -/
structure Constraint (F : Type) where
  a : LinearCombination F
  b : LinearCombination F
  c : LinearCombination F
deriving DecidableEq, Repr

/-- One operation on a bellman constraint system. -/
inductive Operation (F : Type) where
  /-- Allocate the next auxiliary (private) variable, named `name`, with witness function
  `compute`. Ports `ConstraintSystem::alloc` (`lib.rs:385-393`). -/
  | alloc (name : String) (compute : ProverEnvironment F → F)
  /-- Allocate the next input (public) variable, named `name`, with witness function
  `compute`. Ports `ConstraintSystem::alloc_input` (`lib.rs:395-401`). -/
  | allocInput (name : String) (compute : ProverEnvironment F → F)
  /-- Enforce the constraint `c`, named `name`. Ports `ConstraintSystem::enforce`
  (`lib.rs:403-411`). -/
  | enforce (name : String) (c : Constraint F)
  /-- Enter the namespace `name`. Ports `ConstraintSystem::push_namespace` (`lib.rs:413-418`). -/
  | pushNamespace (name : String)
  /-- Leave the current namespace. Ports `ConstraintSystem::pop_namespace` (`lib.rs:420-422`). -/
  | popNamespace

/-- A list of operations, in program order. -/
abbrev Operations (F : Type) := List (Operation F)

/-- The constraints of a list of operations, in the order they were enforced: the rows of the
constraint system. -/
def Operations.constraints : Operations F → List (Constraint F)
  | [] => []
  | .alloc _ _ :: ops => constraints ops
  | .allocInput _ _ :: ops => constraints ops
  | .enforce _ c :: ops => c :: constraints ops
  | .pushNamespace _ :: ops => constraints ops
  | .popNamespace :: ops => constraints ops

end Bellman
