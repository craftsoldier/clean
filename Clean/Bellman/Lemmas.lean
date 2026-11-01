import Clean.Bellman.Semantics

/-!
# Composition lemmas

How the circuit accessors `operations`, `output` and `nextOffset` distribute over the monad
and its primitives, and how the rows of appended operation lists decompose. `circuit_norm`
does not unfold the monad, the accessors or the primitives; it computes through them with
these lemmas, so `simp only [gadget, circuit_norm]` turns a gadget's operations, output and
next offset into those of its primitives.
-/

namespace Bellman

variable {F : Type} {α β : Type}

/-! ## The monad -/

@[circuit_norm]
theorem Circuit.operations_bind (x : Circuit F α) (f : α → Circuit F β) (o : Offset) :
    (x >>= f).operations o = x.operations o ++ (f (x.output o)).operations (x.nextOffset o) :=
  rfl

@[circuit_norm]
theorem Circuit.output_bind (x : Circuit F α) (f : α → Circuit F β) (o : Offset) :
    (x >>= f).output o = (f (x.output o)).output (x.nextOffset o) := rfl

@[circuit_norm]
theorem Circuit.nextOffset_bind (x : Circuit F α) (f : α → Circuit F β) (o : Offset) :
    (x >>= f).nextOffset o = (f (x.output o)).nextOffset (x.nextOffset o) := rfl

@[circuit_norm]
theorem Circuit.operations_pure (a : α) (o : Offset) :
    (pure a : Circuit F α).operations o = [] := rfl

@[circuit_norm]
theorem Circuit.output_pure (a : α) (o : Offset) : (pure a : Circuit F α).output o = a := rfl

@[circuit_norm]
theorem Circuit.nextOffset_pure (a : α) (o : Offset) :
    (pure a : Circuit F α).nextOffset o = o := rfl

/-! ## The primitives -/

@[circuit_norm]
theorem operations_alloc (name : String) (compute : ProverEnvironment F → F) (o : Offset) :
    (alloc name compute).operations o = [.alloc name compute] := rfl

@[circuit_norm]
theorem output_alloc (name : String) (compute : ProverEnvironment F → F) (o : Offset) :
    (alloc name compute).output o = ⟨.aux o.aux⟩ := rfl

@[circuit_norm]
theorem nextOffset_alloc (name : String) (compute : ProverEnvironment F → F) (o : Offset) :
    (alloc name compute).nextOffset o = { o with aux := o.aux + 1 } := rfl

@[circuit_norm]
theorem operations_allocInput (name : String) (compute : ProverEnvironment F → F)
    (o : Offset) : (allocInput name compute).operations o = [.allocInput name compute] := rfl

@[circuit_norm]
theorem output_allocInput (name : String) (compute : ProverEnvironment F → F) (o : Offset) :
    (allocInput name compute).output o = ⟨.input o.input⟩ := rfl

@[circuit_norm]
theorem nextOffset_allocInput (name : String) (compute : ProverEnvironment F → F)
    (o : Offset) : (allocInput name compute).nextOffset o = { o with input := o.input + 1 } :=
  rfl

@[circuit_norm]
theorem operations_enforce (name : String) (a b c : LinearCombination F → LinearCombination F)
    (o : Offset) :
    (enforce name a b c).operations o = [.enforce name ⟨a .zero, b .zero, c .zero⟩] := rfl

@[circuit_norm]
theorem nextOffset_enforce (name : String) (a b c : LinearCombination F → LinearCombination F)
    (o : Offset) : (enforce name a b c).nextOffset o = o := rfl

@[circuit_norm]
theorem operations_withNamespace (name : String) (body : Circuit F α) (o : Offset) :
    (withNamespace name body).operations o
      = .pushNamespace name :: body.operations o ++ [.popNamespace] := rfl

@[circuit_norm]
theorem output_withNamespace (name : String) (body : Circuit F α) (o : Offset) :
    (withNamespace name body).output o = body.output o := rfl

@[circuit_norm]
theorem nextOffset_withNamespace (name : String) (body : Circuit F α) (o : Offset) :
    (withNamespace name body).nextOffset o = body.nextOffset o := rfl

/-! ## Rows -/

/-- The rows of two operation lists in sequence are the first list's rows, then the
second's. -/
@[circuit_norm]
theorem Operations.constraints_append (ops₁ ops₂ : Operations F) :
    Operations.constraints (ops₁ ++ ops₂) = ops₁.constraints ++ ops₂.constraints := by
  induction ops₁ with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [Operations.constraints, ih]

end Bellman
