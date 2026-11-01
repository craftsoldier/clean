import Clean.Bellman.Lemmas

/-!
# The gadget bundle

A gadget's proof boundary is a `FormalCircuit`: its circuit, closed forms of the rows, output
and next offset it emits, what it assumes, what its rows force (`Spec`), and what its honest
prover needs and computes (`ProverAssumptions`, `ProverSpec`), with soundness and completeness.
A parent uses a gadget through these fields only.

## Soundness and completeness

Soundness: on any assignment where ONE holds `1` and the gadget's assumptions hold, if every
row of `rowsAt` holds, so does the spec. Completeness: on an honest assignment
(`ExtendsWitnesses`) where ONE holds `1` and both the assumptions and the prover-side
assumptions hold, every row of `rowsAt` holds, and so does the prover-side spec of the output.

`Assumptions` are hypotheses of both, because a bellman gadget constrains only what its rows
say and its caller supplies the rest: `AllocatedBit::alloc_conditionally` forces its result to
be a bit only when its condition is itself a bit. `ProverAssumptions` are what completeness
alone needs, in addition, so they do not burden soundness: `AllocatedNum::assert_nonzero` is
sound on any input but complete only for a nonzero one (at zero its prover fails). A
prover-side assumption that cannot hold makes completeness vacuous. `ProverSpec` states what
the honest prover's values satisfy beyond what the rows force, so a parent's completeness can
read a child's output value through the call without opening its operations.

`FormalCircuit.constraints_bind` is the emission lemma: after any circuit, a gadget's rows are
that circuit's rows followed by `rowsAt` at the offset it leaves.

## The computed assignment

The assignment a groth16 prover builds: it runs the circuit's witness functions in order,
appending each allocation's value to the inputs or the auxiliary values (`Operations.compute`).
When every witness function reads only variables allocated before it
(`Operations.ComputableWitnesses`), that assignment is honest in the sense of
`ExtendsWitnesses` (`Operations.extendsWitnesses_compute`), so a gadget's completeness applies
to it (`FormalCircuit.complete_computed`).

## Reading only earlier variables

A witness function reads a whole environment, so nothing stops it from reading a variable
allocated after it; the step-by-step assignment then reads 0 there, and need not be honest.
`ComputableWitnesses ops o` rules this out: each witness function, at its offset, returns the
same value on any two environments that agree on the variables allocated before it and on the
hint. A gadget's witness functions read its input, so a gadget is computable for an input
allocated before its offset (`HasBelow`). They may also read ONE, input 0, which the groth16
prover allocates before the circuit, so computability is stated at offsets past it. A gadget's
output is allocated before the offset after it, so a parent can pass it on to another gadget.

## Rust references (bellman 0.15.0, groth16 0.2.0)

- bellman `src/gadgets/boolean.rs` — `AllocatedBit::alloc_conditionally`
- bellman `src/gadgets/num.rs` — `AllocatedNum::assert_nonzero`
- groth16 `src/prover.rs` — `create_proof`, `ProvingAssignment::alloc` and `alloc_input`
-/

namespace Bellman

variable {F : Type}

/-! ### Offsets -/

/-- The offset after a list of operations, from offset `o`. -/
def Operations.advance : Operations F → Offset → Offset
  | [], o => o
  | op :: ops, o => advance ops (op.advance o)

/-- A variable allocated before offset `o`. -/
def Variable.Below (o : Offset) : Variable → Prop
  | ⟨.input i⟩ => i < o.input
  | ⟨.aux j⟩ => j < o.aux

theorem Variable.Below.mono {v : Variable} {o o' : Offset} (h : v.Below o)
    (hi : o.input ≤ o'.input) (ha : o.aux ≤ o'.aux) : v.Below o' := by
  rcases v with ⟨i | j⟩
  · exact Nat.lt_of_lt_of_le h hi
  · exact Nat.lt_of_lt_of_le h ha

/-- Values whose variables are all allocated before an offset. -/
class HasBelow (α : Type) where
  /-- Every variable of the value is allocated before the offset. -/
  Below : α → Offset → Prop
  /-- Allocated before an offset, so before any later one. -/
  mono : ∀ {x : α} {o o' : Offset}, Below x o → o.input ≤ o'.input → o.aux ≤ o'.aux →
    Below x o'

instance : HasBelow Variable := ⟨fun v o => v.Below o, fun h hi ha => h.mono hi ha⟩

instance : HasBelow Unit := ⟨fun _ _ => True, fun _ _ _ => trivial⟩

instance {α β : Type} [HasBelow α] [HasBelow β] : HasBelow (α × β) :=
  ⟨fun x o => HasBelow.Below x.1 o ∧ HasBelow.Below x.2 o,
    fun h hi ha => ⟨HasBelow.mono h.1 hi ha, HasBelow.mono h.2 hi ha⟩⟩

/-- A value captured by the circuit, as bellman's `Option` witnesses are, holds no variable. -/
instance {W : Type} : HasBelow (Option W) := ⟨fun _ _ => True, fun _ _ _ => trivial⟩

/-! ### The step-by-step assignment -/

/-- The prover environment holding two lists of values, reading 0 past their ends. -/
def ProverEnvironment.ofLists [Zero F] (inputs aux : List F) (hint : ProverHint F) :
    ProverEnvironment F :=
  { input := fun i => inputs[i]?.getD 0, aux := fun j => aux[j]?.getD 0, hint }

/-- Run the witness functions in order, each on the values so far, appending its value to the
inputs or the auxiliary values, as the groth16 prover pushes `f()` at each allocation.
Starting from inputs `[1]`, the value of ONE, and no auxiliary values, this is the assignment
`create_proof` builds (`prover.rs:181-206`). -/
def Operations.compute [Zero F] (hint : ProverHint F) :
    Operations F → List F × List F → List F × List F
  | [], s => s
  | .alloc _ f :: ops, (ins, aux) =>
    compute hint ops (ins, aux ++ [f (.ofLists ins aux hint)])
  | .allocInput _ f :: ops, (ins, aux) =>
    compute hint ops (ins ++ [f (.ofLists ins aux hint)], aux)
  | .enforce _ _ :: ops, s => compute hint ops s
  | .pushNamespace _ :: ops, s => compute hint ops s
  | .popNamespace :: ops, s => compute hint ops s

/-- The computed values extend the values it starts from. -/
theorem Operations.compute_extends [Zero F] (hint : ProverHint F) :
    ∀ (ops : Operations F) (ins aux : List F),
      ∃ ins₂ aux₂, ops.compute hint (ins, aux) = (ins ++ ins₂, aux ++ aux₂)
  | [], ins, aux => ⟨[], [], by simp [compute]⟩
  | .alloc _ f :: ops, ins, aux => by
    obtain ⟨i₂, a₂, h⟩ := compute_extends hint ops ins (aux ++ [f (.ofLists ins aux hint)])
    exact ⟨i₂, f (.ofLists ins aux hint) :: a₂,
      by simp only [compute, h, List.append_assoc, List.singleton_append]⟩
  | .allocInput _ f :: ops, ins, aux => by
    obtain ⟨i₂, a₂, h⟩ := compute_extends hint ops (ins ++ [f (.ofLists ins aux hint)]) aux
    exact ⟨f (.ofLists ins aux hint) :: i₂, a₂,
      by simp only [compute, h, List.append_assoc, List.singleton_append]⟩
  | .enforce _ _ :: ops, ins, aux => by
    have := compute_extends hint ops ins aux; simp_all [compute]
  | .pushNamespace _ :: ops, ins, aux => by
    have := compute_extends hint ops ins aux; simp_all [compute]
  | .popNamespace :: ops, ins, aux => by
    have := compute_extends hint ops ins aux; simp_all [compute]

/-! ### Reading only earlier variables -/

/-- Two prover environments agree on the variables before offset `o`, and have the same hint. -/
def ProverEnvironment.AgreesBelow (o : Offset) (e e' : ProverEnvironment F) : Prop :=
  (∀ i < o.input, e.input i = e'.input i) ∧ (∀ j < o.aux, e.aux j = e'.aux j) ∧
    e.hint = e'.hint

/-- A variable allocated before `o` reads the same on two environments that agree before `o`. -/
theorem Variable.get_agrees {v : Variable} {o : Offset} {e e' : ProverEnvironment F}
    (hv : v.Below o) (h : e.AgreesBelow o e') :
    e.toEnvironment.get v = e'.toEnvironment.get v := by
  rcases v with ⟨i | j⟩
  · exact h.1 i hv
  · exact h.2.1 j hv

/-- Each witness function in `ops`, from offset `o`, reads only the variables allocated before
it and the hint (see the module docstring). -/
def Operations.ComputableWitnesses : Operations F → Offset → Prop
  | [], _ => True
  | .alloc _ f :: ops, o =>
    (∀ e e' : ProverEnvironment F, e.AgreesBelow o e' → f e = f e') ∧
      ComputableWitnesses ops { o with aux := o.aux + 1 }
  | .allocInput _ f :: ops, o =>
    (∀ e e' : ProverEnvironment F, e.AgreesBelow o e' → f e = f e') ∧
      ComputableWitnesses ops { o with input := o.input + 1 }
  | .enforce _ _ :: ops, o => ComputableWitnesses ops o
  | .pushNamespace _ :: ops, o => ComputableWitnesses ops o
  | .popNamespace :: ops, o => ComputableWitnesses ops o

/-- **The computed assignment is honest.** When every witness function reads only earlier
variables, the step-by-step assignment, started from values whose counts are the offset,
satisfies `ExtendsWitnesses`. -/
theorem Operations.extendsWitnesses_compute [Zero F] (hint : ProverHint F) :
    ∀ (ops : Operations F) (ins aux : List F),
      ops.ComputableWitnesses ⟨ins.length, aux.length⟩ →
      ExtendsWitnesses
        (.ofLists (ops.compute hint (ins, aux)).1 (ops.compute hint (ins, aux)).2 hint)
        ops ⟨ins.length, aux.length⟩
  | [], _, _, _ => trivial
  | .alloc _ f :: ops, ins, aux, ⟨hf, hops⟩ => by
    obtain ⟨i₂, a₂, h⟩ := compute_extends hint ops ins (aux ++ [f (.ofLists ins aux hint)])
    simp only [compute, ExtendsWitnesses, Operation.ExtendsWitness, Operation.advance]
    refine ⟨?_, ?_⟩
    · rw [h]
      -- the final environment agrees with the one `f` ran on, below its offset
      have hagree : ProverEnvironment.AgreesBelow ⟨ins.length, aux.length⟩
          (.ofLists (ins ++ i₂) (aux ++ [f (.ofLists ins aux hint)] ++ a₂) hint)
          (.ofLists ins aux hint) := by
        refine ⟨fun i hi => ?_, fun j hj => ?_, rfl⟩
        · simp [ProverEnvironment.ofLists, List.getElem?_append_left hi]
        · simp [ProverEnvironment.ofLists, List.append_assoc, List.getElem?_append_left hj]
      rw [hf _ _ hagree]
      simp [ProverEnvironment.ofLists, List.append_assoc]
    · have := extendsWitnesses_compute hint ops ins (aux ++ [f (.ofLists ins aux hint)])
        (by simp only [List.length_append, List.length_singleton]; exact hops)
      simp only [List.length_append, List.length_singleton] at this
      exact this
  | .allocInput _ f :: ops, ins, aux, ⟨hf, hops⟩ => by
    obtain ⟨i₂, a₂, h⟩ := compute_extends hint ops (ins ++ [f (.ofLists ins aux hint)]) aux
    simp only [compute, ExtendsWitnesses, Operation.ExtendsWitness, Operation.advance]
    refine ⟨?_, ?_⟩
    · rw [h]
      -- the final environment agrees with the one `f` ran on, below its offset
      have hagree : ProverEnvironment.AgreesBelow ⟨ins.length, aux.length⟩
          (.ofLists (ins ++ [f (.ofLists ins aux hint)] ++ i₂) (aux ++ a₂) hint)
          (.ofLists ins aux hint) := by
        refine ⟨fun i hi => ?_, fun j hj => ?_, rfl⟩
        · simp [ProverEnvironment.ofLists, List.append_assoc, List.getElem?_append_left hi]
        · simp [ProverEnvironment.ofLists, List.getElem?_append_left hj]
      rw [hf _ _ hagree]
      simp [ProverEnvironment.ofLists, List.append_assoc]
    · have := extendsWitnesses_compute hint ops (ins ++ [f (.ofLists ins aux hint)]) aux
        (by simp only [List.length_append, List.length_singleton]; exact hops)
      simp only [List.length_append, List.length_singleton] at this
      exact this
  | .enforce _ _ :: ops, ins, aux, hops => by
    have := extendsWitnesses_compute hint ops ins aux hops
    simp_all [compute, ExtendsWitnesses, Operation.ExtendsWitness, Operation.advance]
  | .pushNamespace _ :: ops, ins, aux, hops => by
    have := extendsWitnesses_compute hint ops ins aux hops
    simp_all [compute, ExtendsWitnesses, Operation.ExtendsWitness, Operation.advance]
  | .popNamespace :: ops, ins, aux, hops => by
    have := extendsWitnesses_compute hint ops ins aux hops
    simp_all [compute, ExtendsWitnesses, Operation.ExtendsWitness, Operation.advance]

/-! ### The bundle -/

/-- A gadget: its circuit, closed forms of what it emits, its assumptions and its spec, and its
prover-side assumptions and spec, with soundness and completeness (see the module docstring). -/
structure FormalCircuit (F : Type) [Ring F] (α β : Type) [HasBelow α] [HasBelow β] where
  /-- The gadget's circuit, on its input. -/
  main : α → Circuit F β
  /-- The rows it emits from an offset. -/
  rowsAt : α → Offset → List (Constraint F)
  rowsAt_eq : ∀ x o, ((main x).operations o).constraints = rowsAt x o := by intros; rfl
  /-- Its output from an offset. -/
  output : α → Offset → β
  output_eq : ∀ x o, (main x).output o = output x o := by intros; rfl
  /-- The offset after its allocations. -/
  nextOffset : α → Offset → Offset
  nextOffset_eq : ∀ x o, (main x).nextOffset o = nextOffset x o := by intros; rfl
  advance_eq : ∀ x o, ((main x).operations o).advance o = nextOffset x o := by intros; rfl
  /-- Its witness functions read only variables allocated before them, at an offset past ONE
  and for an input allocated before that offset. -/
  computable : ∀ x o, 0 < o.input → HasBelow.Below x o →
    ((main x).operations o).ComputableWitnesses o
  /-- Its output is allocated before the offset after it. -/
  output_below : ∀ x o, HasBelow.Below x o → HasBelow.Below (output x o) (nextOffset x o)
  /-- What it needs of its input and the assignment, for soundness and completeness. -/
  Assumptions : Environment F → α → Prop := fun _ _ => True
  /-- What its rows force. -/
  Spec : Environment F → α → β → Prop
  /-- What its honest prover needs besides `Assumptions`, for completeness only. -/
  ProverAssumptions : ProverEnvironment F → α → Prop := fun _ _ => True
  /-- What the values its honest prover computes satisfy, proved alongside its rows. -/
  ProverSpec : ProverEnvironment F → α → β → Prop := fun _ _ _ => True
  soundness : ∀ (o : Offset) (env : Environment F) (x : α), env.input 0 = 1 →
    Assumptions env x → (∀ r ∈ rowsAt x o, r.Holds env) → Spec env x (output x o)
  completeness : ∀ (o : Offset) (env : ProverEnvironment F) (x : α), env.input 0 = 1 →
    Assumptions env x → ProverAssumptions env x →
    ExtendsWitnesses env ((main x).operations o) o →
    (∀ r ∈ rowsAt x o, r.Holds env) ∧ ProverSpec env x (output x o)

variable [Ring F] {α β : Type} [HasBelow α] [HasBelow β]

/-- **The emission lemma.** After any circuit `p`, the rows are `p`'s rows followed by the
gadget's rows at the offset `p` leaves. -/
theorem FormalCircuit.constraints_bind {γ : Type} (G : FormalCircuit F α β) (p : Circuit F γ)
    (f : γ → α) (o : Offset) :
    ((p >>= fun y => G.main (f y)).operations o).constraints
      = (p.operations o).constraints ++ G.rowsAt (f (p.output o)) (p.nextOffset o) := by
  rw [Circuit.operations_bind, Operations.constraints_append, G.rowsAt_eq]

/-- The assignment the prover computes for the gadget on `x` from offset `o`, continuing from
the values `ins` and `aux`. -/
def FormalCircuit.computedEnv (G : FormalCircuit F α β) (hint : ProverHint F) (x : α)
    (o : Offset) (ins aux : List F) : ProverEnvironment F :=
  let s := ((G.main x).operations o).compute hint (ins, aux)
  .ofLists s.1 s.2 hint

/-- **Completeness on the computed assignment.** Started from values whose counts are the
offset and whose first input is `1`, the assignment the witness functions compute satisfies
every row and the prover-side spec, for an input allocated before the offset and given the
gadget's assumptions and prover-side assumptions on that assignment. -/
theorem FormalCircuit.complete_computed (G : FormalCircuit F α β) (hint : ProverHint F) (x : α)
    (o : Offset) (ins aux : List F) (hi : ins.length = o.input) (ha : aux.length = o.aux)
    (h1 : ins.head? = some 1) (hx : HasBelow.Below x o)
    (hA : G.Assumptions (G.computedEnv hint x o ins aux).toEnvironment x)
    (hP : G.ProverAssumptions (G.computedEnv hint x o ins aux) x) :
    (∀ r ∈ G.rowsAt x o, r.Holds (G.computedEnv hint x o ins aux).toEnvironment) ∧
      G.ProverSpec (G.computedEnv hint x o ins aux) x (G.output x o) := by
  obtain ⟨i₂, a₂, hs⟩ := Operations.compute_extends hint ((G.main x).operations o) ins aux
  -- ONE is the first of the values it starts from, so the offset is past it
  have hpos : 0 < o.input := by
    rw [← hi]; rcases ins with _ | _
    · simp at h1
    · simp
  refine G.completeness _ _ x ?_ hA hP ?_
  · show (((G.main x).operations o).compute hint (ins, aux)).1[0]?.getD 0 = 1
    rw [hs]
    rcases ins with _ | ⟨a, ins⟩
    · simp at h1
    · simp only [List.head?_cons, Option.some.injEq] at h1
      simp [h1]
  · have ho : o = ⟨ins.length, aux.length⟩ := by rw [hi, ha]
    subst ho
    exact Operations.extendsWitnesses_compute hint _ ins aux (G.computable x _ hpos hx)

end Bellman
