import Clean.Bellman.Formal

/-!
# Calls

A parent circuit uses a gadget by calling it (`FormalCircuit.call`): the child's operations are
appended inline, as bellman emits them, and the parent's proofs see only the child's bundle,
its closed forms, soundness and completeness.

## The call boundary

`call` goes through an opaque constant, so neither tactics nor definitional checks see a
child's operations, and a parent's proof keeps them folded however deep the tree of calls. The
lemmas here are the way in. `output_call`, `nextOffset_call`, `constraints_call` and
`advance_call`, in `circuit_norm`, give the child's output, next offset, rows and the offset its
operations reach; `computable_call` and `completeness_call` give its computability and
completeness. `operations_call` opens its operations and is not in `circuit_norm`.

## Operations in sequence

A parent's operations are its parts' in sequence (`Circuit.operations_bind`). The offset,
honesty and computability of a sequence split at the offset the first part leaves
(`Operations.advance_append`, `extendsWitnesses_append`,
`Operations.computableWitnesses_append`, all in `circuit_norm`), and that offset is never below
the one it started from (`Operations.le_advance`; for a gadget, `FormalCircuit.le_nextOffset`),
so variables allocated before a call stay allocated after it.
-/

namespace Bellman
variable {F : Type}

/-! ### Operation lists in sequence -/

/-- The offset after two operation lists in sequence: the second's, from where the first
leaves it. -/
@[circuit_norm]
theorem Operations.advance_append (ops₁ ops₂ : Operations F) (o : Offset) :
    (ops₁ ++ ops₂).advance o = ops₂.advance (ops₁.advance o) := by
  induction ops₁ generalizing o with
  | nil => rfl
  | cons op ops ih => exact ih _

/-- Offsets only grow: the offset after a list of operations is at least the one it starts
from. -/
theorem Operations.le_advance (ops : Operations F) (o : Offset) :
    o.input ≤ (ops.advance o).input ∧ o.aux ≤ (ops.advance o).aux := by
  induction ops generalizing o with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons op ops ih =>
    obtain ⟨h₁, h₂⟩ := ih (op.advance o)
    cases op <;> simp only [Operations.advance, Operation.advance] at h₁ h₂ ⊢ <;> omega

/-- An assignment is honest for two operation lists in sequence exactly when it is for each,
the second from where the first leaves the offset. -/
@[circuit_norm]
theorem extendsWitnesses_append (env : ProverEnvironment F) (ops₁ ops₂ : Operations F)
    (o : Offset) :
    ExtendsWitnesses env (ops₁ ++ ops₂) o ↔
      ExtendsWitnesses env ops₁ o ∧ ExtendsWitnesses env ops₂ (ops₁.advance o) := by
  induction ops₁ generalizing o with
  | nil => simp [ExtendsWitnesses, Operations.advance]
  | cons op ops ih =>
    simp only [List.cons_append, ExtendsWitnesses, Operations.advance, ih, and_assoc]

/-- Two lists of operations in sequence read only earlier variables exactly when each does,
the second from where the first leaves the offset. -/
@[circuit_norm]
theorem Operations.computableWitnesses_append (ops₁ ops₂ : Operations F) (o : Offset) :
    (ops₁ ++ ops₂).ComputableWitnesses o ↔
      ops₁.ComputableWitnesses o ∧ ops₂.ComputableWitnesses (ops₁.advance o) := by
  induction ops₁ generalizing o with
  | nil => simp [ComputableWitnesses, advance]
  | cons op ops ih =>
    cases op <;> simp only [List.cons_append, ComputableWitnesses, advance, Operation.advance,
      ih, and_assoc]

/-! ### The call -/

/-- A call's output, operations and next offset, behind an `opaque` barrier, with their
defining equation recorded: no tactic or definitional check sees through a call, and a parent
reaches its child only through the lemmas below. -/
private opaque callPacked (F : Type) [Ring F] (α β : Type) [HasBelow α] [HasBelow β] :
    { f : FormalCircuit F α β → α → Circuit F β //
      ∀ G x o, f G x o = (G.output x o, (G.main x).operations o, G.nextOffset x o) } :=
  ⟨fun G x o => (G.output x o, (G.main x).operations o, G.nextOffset x o), fun _ _ _ => rfl⟩

variable [Ring F] {α β : Type} [HasBelow α] [HasBelow β]

/-- Call a gadget from a parent circuit: the child's operations are appended inline, as
bellman emits them, and its output and next offset are the bundle's closed forms. -/
def FormalCircuit.call (G : FormalCircuit F α β) (x : α) : Circuit F β :=
  fun o => (callPacked F α β).val G x o

/-- The call's defining equation. -/
theorem FormalCircuit.call_eq (G : FormalCircuit F α β) (x : α) (o : Offset) :
    G.call x o = (G.output x o, (G.main x).operations o, G.nextOffset x o) :=
  (callPacked F α β).property G x o

@[circuit_norm]
theorem FormalCircuit.output_call (G : FormalCircuit F α β) (x : α) (o : Offset) :
    (G.call x).output o = G.output x o := by
  show (G.call x o).1 = _; rw [G.call_eq]

@[circuit_norm]
theorem FormalCircuit.nextOffset_call (G : FormalCircuit F α β) (x : α) (o : Offset) :
    (G.call x).nextOffset o = G.nextOffset x o := by
  show (G.call x o).2.2 = _; rw [G.call_eq]

/-- A call's operations are the child's. Not `@[circuit_norm]`: a parent proof keeps the
child's operations folded and opens them only through this lemma. -/
theorem FormalCircuit.operations_call (G : FormalCircuit F α β) (x : α) (o : Offset) :
    (G.call x).operations o = (G.main x).operations o := by
  show (G.call x o).2.1 = _; rw [G.call_eq]

/-- A call's rows are the child's `rowsAt`. -/
@[circuit_norm]
theorem FormalCircuit.constraints_call (G : FormalCircuit F α β) (x : α) (o : Offset) :
    ((G.call x).operations o).constraints = G.rowsAt x o := by
  rw [G.operations_call]; exact G.rowsAt_eq x o

/-- Walking a call's operations reaches the child's closed-form next offset. -/
@[circuit_norm]
theorem FormalCircuit.advance_call (G : FormalCircuit F α β) (x : α) (o : Offset) :
    ((G.call x).operations o).advance o = G.nextOffset x o := by
  rw [G.operations_call]; exact G.advance_eq x o

/-- Offsets only grow across a gadget: the offset after it is at least the one it starts
from. -/
theorem FormalCircuit.le_nextOffset (G : FormalCircuit F α β) (x : α) (o : Offset) :
    o.input ≤ (G.nextOffset x o).input ∧ o.aux ≤ (G.nextOffset x o).aux := by
  rw [← G.advance_eq]; exact Operations.le_advance _ o

/-- A call's witness functions read only variables allocated before them, at an offset past
ONE and for an input allocated before that offset. -/
theorem FormalCircuit.computable_call (G : FormalCircuit F α β) (x : α) (o : Offset)
    (ho : 0 < o.input) (hx : HasBelow.Below x o) :
    ((G.call x).operations o).ComputableWitnesses o := by
  rw [G.operations_call]; exact G.computable x o ho hx

/-- On an assignment honest for a call, where ONE holds `1` and the child's assumptions hold,
the child's completeness gives its rows. -/
theorem FormalCircuit.completeness_call (G : FormalCircuit F α β) (o : Offset)
    (env : ProverEnvironment F) (x : α) (h1 : env.input 0 = 1) (hA : G.Assumptions env x)
    (h : ExtendsWitnesses env ((G.call x).operations o) o) :
    ∀ r ∈ G.rowsAt x o, r.Holds env :=
  G.completeness o env x h1 hA (G.operations_call x o ▸ h)

end Bellman
