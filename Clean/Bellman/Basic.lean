import Clean.Bellman.ConstraintSystem

/-!
# The bellman circuit monad

`Circuit F α` is what a bellman circuit is in Lean: run from an `Offset`, it returns its output,
the operations it performs in program order, and the offset after its allocations. Its
primitives port bellman's `ConstraintSystem` methods: `alloc`, `allocInput`, `enforce` and
`withNamespace`.

## Normal forms

The monad, its accessors `operations`, `output`, `nextOffset` and the primitives are the
normal forms of circuit proofs and are not unfolded by `circuit_norm`; lemmas about how they
compose are added where a proof first needs them.

## Rust references (bellman 0.15.0, groth16 0.2.0)

- `src/lib.rs` — `ConstraintSystem`, `Namespace`
- `src/gadgets/test/mod.rs` — `TestConstraintSystem`
- groth16 `src/generator.rs`, `src/prover.rs`
-/

namespace Bellman

variable {F : Type} {α : Type}

/-- A bellman circuit: from the offset it starts at, its output, its operations in program
order, and the offset after its allocations. -/
def Circuit (F : Type) (α : Type) :=
  Offset → α × Operations F × Offset

namespace Circuit

instance : Monad (Circuit F) where
  pure a := fun o => (a, [], o)
  bind x f := fun o =>
    let (a, ops, o') := x o
    let (b, ops', o'') := f a o'
    (b, ops ++ ops', o'')

/-- The operations of a circuit, from a given offset (by default, a whole circuit's start). -/
def operations (circuit : Circuit F α) (o : Offset := Offset.start) : Operations F :=
  (circuit o).2.1

/-- The output of a circuit, from a given offset (by default, a whole circuit's start). -/
def output (circuit : Circuit F α) (o : Offset := Offset.start) : α :=
  (circuit o).1

/-- The offset after a circuit's allocations, from a given offset (by default, a whole
circuit's start). -/
def nextOffset (circuit : Circuit F α) (o : Offset := Offset.start) : Offset :=
  (circuit o).2.2

end Circuit

/-- Allocate the next auxiliary (private) variable. Ports `ConstraintSystem::alloc`
(`lib.rs:385-393`): it is `Aux` of the count of auxiliary variables allocated so far
(`TestConstraintSystem::alloc`, `test/mod.rs:363-376`). groth16's prover runs the corresponding
closure once, at the allocation, in program order (`prover.rs:76-89`); its key generator never
runs it (`generator.rs:58-75`). -/
def alloc (name : String) (compute : ProverEnvironment F → F) : Circuit F Variable :=
  fun o => (⟨.aux o.aux⟩, [.alloc name compute], { o with aux := o.aux + 1 })

/-- Allocate the next input (public) variable. Ports `ConstraintSystem::alloc_input`
(`lib.rs:395-401`; `TestConstraintSystem::alloc_input`, `test/mod.rs:378-391`). Inputs have
witness functions too: the prover computes the public inputs (groth16 `prover.rs:91-103`). -/
def allocInput (name : String) (compute : ProverEnvironment F → F) : Circuit F Variable :=
  fun o => (⟨.input o.input⟩, [.allocInput name compute], { o with input := o.input + 1 })

/-- Enforce `A · B = C`, each linear combination built by applying its closure to the empty
one. Ports `ConstraintSystem::enforce` (`lib.rs:403-411`; `TestConstraintSystem::enforce`,
`test/mod.rs:393-410`). -/
def enforce (name : String) (a b c : LinearCombination F → LinearCombination F) :
    Circuit F Unit :=
  fun o => ((), [.enforce name ⟨a .zero, b .zero, c .zero⟩], o)

/-- Run `body` inside the namespace `name`: its operations between a `pushNamespace` and a
`popNamespace`, with offsets unchanged by either. Ports `ConstraintSystem::namespace`
(`lib.rs:428-437`), which pushes the namespace and pops it when the returned `Namespace` is
dropped (`lib.rs:506-510`). Named `withNamespace` because `namespace` is a Lean keyword. -/
def withNamespace (name : String) (body : Circuit F α) : Circuit F α :=
  fun o =>
    let (a, ops, o') := body o
    (a, .pushNamespace name :: ops ++ [.popNamespace], o')

end Bellman
