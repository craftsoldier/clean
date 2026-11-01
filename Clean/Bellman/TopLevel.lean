import Clean.Bellman.Subcircuit

/-!
# The top level

A top-level circuit is the circuit groth16 runs: a `FormalCircuit` over the prover's private
data, captured as `Option` values as in bellman's circuit structs (`TopLevelCircuit`), with the
statement it proves. Key generation runs it with every private value `none`, without running any
witness function, so its rows and its next offset must not depend on that data; and no enclosing
circuit supplies its assumptions, so it has none. Its prover-side assumptions remain, as a
hypothesis of completeness.

## The key's rows and the relation

Key generation allocates ONE, runs the circuit, then appends `Input(i) · 0 = 0` for every input
`i`, ONE included (`extraRows`). These rows hold on every assignment (`extraRows_holds`), so they
change nothing about which assignments satisfy the key; bellman's `TestConstraintSystem` does not
record them. `keyRows` is the circuit's rows from the start followed by them. `Relation x` is
the relation they pin on public inputs `x`: the number of inputs, ONE included, is
`x.length + 1`, and some auxiliary values satisfy every key row with inputs `(1, x)`
(`withPublic`). This is the relation of Groth, *On the Size of Pairing-based Non-interactive
Arguments* (2016), §2.3, with the count the verifier checks; it says nothing about the pairing
check itself.

## The statement

The public input is a typed value (`PublicInput`, a `ProvableType`), read from the inputs after
ONE (`extractPublicInput`), which it fills exactly. The private witness is read from the whole
assignment (`extractPrivate`). `Spec` is the statement's condition on the two, and the formal
circuit's spec gives it at the values read from any assignment (`spec_of`). A gadget's spec names
variables only through its input and output, so the statement can rely only on what it says of
the variables the formal circuit outputs. `Statement p` says some private witness satisfies
`Spec` at `p`.

## Soundness and completeness

Soundness: an assignment with inputs `(1, x)` satisfying the key's rows satisfies `Spec`, at the
public input read from `x` and the private witness read from the assignment; so public inputs in
the relation satisfy the statement (`statement_soundness`). Completeness: for any private data,
given the circuit's prover-side assumptions on the assignment the prover computes, the public
inputs it computes, from inputs `[1]` and no auxiliary values, are in the relation, and the
prover-side spec holds on that assignment.

## Independence through calls

A parent built from calls cannot show by `rfl` that its rows ignore the private data: the calls
are opaque. `FormalCircuit.Indep` states it for a gadget's closed forms, a parent proves it from
its children's, and a top-level circuit's `rows_indep` and `nextOffset_indep` follow from it.

## Rust references (groth16 0.2.0)

- groth16 `src/generator.rs` — `generate_parameters`, `KeypairAssembly::alloc`
- groth16 `src/prover.rs` — `create_proof`
- groth16 `src/verifier.rs` — `verify_proof`
-/

namespace Bellman
variable {F : Type}

section
variable [Zero F]

/-- `Operations.compute` returns as many inputs and auxiliary values as the offset the operations
walk to, from the counts it starts with. -/
theorem Operations.compute_length (hint : ProverHint F) :
    ∀ (ops : Operations F) (ins aux : List F),
      (⟨(ops.compute hint (ins, aux)).1.length, (ops.compute hint (ins, aux)).2.length⟩ :
        Offset) = ops.advance ⟨ins.length, aux.length⟩
  | [], _, _ => rfl
  | .alloc _ f :: ops, ins, aux => by
    have h := compute_length hint ops ins (aux ++ [f (.ofLists ins aux hint)])
    simp only [List.length_append, List.length_singleton] at h
    exact h
  | .allocInput _ f :: ops, ins, aux => by
    have h := compute_length hint ops (ins ++ [f (.ofLists ins aux hint)]) aux
    simp only [List.length_append, List.length_singleton] at h
    exact h
  | .enforce _ _ :: ops, ins, aux => compute_length hint ops ins aux
  | .pushNamespace _ :: ops, ins, aux => compute_length hint ops ins aux
  | .popNamespace :: ops, ins, aux => compute_length hint ops ins aux

end

variable [Ring F]

/-- The rows `Input(i) · 0 = 0` for the inputs `0, …, n − 1`, which key generation and the
prover append after the circuit (`generator.rs:193-202`, `prover.rs:208-215`). -/
def extraRows (n : ℕ) : List (Constraint F) :=
  (List.range n).map fun i =>
    ⟨(LinearCombination.zero : LinearCombination F) + (⟨.input i⟩ : Variable), .zero, .zero⟩

/-- Every row of `extraRows` holds on every assignment. -/
theorem extraRows_holds (env : Environment F) (n : ℕ) : ∀ r ∈ extraRows n, r.Holds env := by
  intro r hr
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hr
  simp [Constraint.holds_def, circuit_norm]

/-- The assignment with inputs `1, x₁, …, xₙ`, reading 0 past them, and the given auxiliary
values. -/
def withPublic (x : List F) (aux : ℕ → F) : Environment F :=
  ⟨fun i => (1 :: x)[i]?.getD 0, aux⟩

section
variable {PublicInput : TypeMap} [ProvableType PublicInput]

/-- The public input read from an assignment: inputs `1, …, size`, after ONE. -/
def extractPublicInput (env : Environment F) : PublicInput F :=
  fromElements (Vector.ofFn fun i : Fin (size PublicInput) => env.input (i.val + 1))

/-- The public input read from the list of public inputs the verifier is given. -/
def readPublicInput (x : List F) : PublicInput F :=
  fromElements (Vector.ofFn fun i : Fin (size PublicInput) => x.getD i.val 0)

/-- With inputs `(1, x)`, the public input read from the assignment is the one read from `x`. -/
theorem extractPublicInput_withPublic (x : List F) (aux : ℕ → F) :
    extractPublicInput (PublicInput := PublicInput) (withPublic x aux) = readPublicInput x := by
  simp only [extractPublicInput, readPublicInput, withPublic, List.getElem?_cons_succ,
    List.getD_eq_getElem?_getD]

end

/-- A circuit groth16 runs, with the statement it proves: a formal circuit over the prover's
private data, whose rows and next offset do not depend on that data, since key generation runs it
with `none` and no witness function (`generator.rs:58-70, 187-191`), and which has no
`Assumptions`; a public input filling the inputs after ONE; and a private witness and a spec,
which the formal circuit's spec gives. -/
structure TopLevelCircuit (F : Type) [Ring F] (W β : Type) [HasBelow β]
    (PublicInput : TypeMap) [ProvableType PublicInput] where
  /-- The underlying formal circuit, over the private data. -/
  formalCircuit : FormalCircuit F (Option W) β
  /-- Its rows do not depend on the private data. -/
  rows_indep : ∀ w o, formalCircuit.rowsAt w o = formalCircuit.rowsAt none o
  /-- Nor does its next offset. -/
  nextOffset_indep : ∀ w o, formalCircuit.nextOffset w o = formalCircuit.nextOffset none o
  /-- A top-level circuit has no assumptions supplied by an enclosing circuit. -/
  assumptions_eq : formalCircuit.Assumptions = fun _ _ => True
  /-- The public input fills every input after ONE. -/
  numInputs_eq : (formalCircuit.nextOffset none Offset.start).input = size PublicInput + 1
  /-- The part of the statement's witness that is not public. -/
  PrivateWitness : Type
  /-- The private witness read from an assignment. -/
  extractPrivate : Environment F → PrivateWitness
  /-- The statement's condition, on the public input and the private witness. -/
  Spec : PublicInput F → PrivateWitness → Prop
  /-- The formal circuit's spec gives it, at the public input and the private witness read from
  the assignment. -/
  spec_of : ∀ env, formalCircuit.Spec env none (formalCircuit.output none Offset.start) →
    Spec (extractPublicInput env) (extractPrivate env)

namespace TopLevelCircuit

variable {W β : Type} [HasBelow β] {PublicInput : TypeMap} [ProvableType PublicInput]
  (self : TopLevelCircuit F W β PublicInput)

/-- The number of inputs, ONE included: the verifying key's `ic.len()`. -/
def numInputs : ℕ := (self.formalCircuit.nextOffset none Offset.start).input

/-- The rows key generation produces: the circuit's rows from the start, then `extraRows` for
every input (`generator.rs:187-202`). -/
def keyRows : List (Constraint F) :=
  self.formalCircuit.rowsAt none Offset.start ++ extraRows self.numInputs

/-- The relation the key's rows pin on public inputs `x`: `x` has one entry for each input after
ONE, as the verifier requires (`verifier.rs:28`), and some auxiliary values satisfy every key row
with inputs `(1, x)`. -/
def Relation (x : List F) : Prop :=
  x.length + 1 = self.numInputs ∧ ∃ aux, ∀ r ∈ self.keyRows, r.Holds (withPublic x aux)

/-- Some private witness satisfies the spec at the public input `p`. -/
def Statement (p : PublicInput F) : Prop := ∃ w, self.Spec p w

/-- **Soundness.** An assignment with inputs `(1, x)` satisfying every key row satisfies the
spec, at the public input read from `x` and the private witness read from the assignment. -/
theorem soundness (x : List F) (aux : ℕ → F)
    (h : ∀ r ∈ self.keyRows, r.Holds (withPublic x aux)) :
    self.Spec (readPublicInput x) (self.extractPrivate (withPublic x aux)) := by
  rw [← extractPublicInput_withPublic x aux]
  exact self.spec_of _ (self.formalCircuit.soundness _ _ none rfl
    (by rw [self.assumptions_eq]; trivial) fun r hr => h r (List.mem_append_left _ hr))

/-- **Statement soundness.** Public inputs in the relation satisfy the statement. -/
theorem statement_soundness (x : List F) (h : self.Relation x) :
    self.Statement (readPublicInput x) :=
  let ⟨_, aux, hrows⟩ := h
  ⟨_, self.soundness x aux hrows⟩

/-- **Completeness.** For any private data, given the prover-side assumptions on the assignment
the prover computes, the public inputs it computes, starting from inputs `[1]` and no auxiliary
values (`prover.rs:204-206`), are in the relation, and the prover-side spec holds on that
assignment. -/
theorem completeness (hint : ProverHint F) (w : W)
    (hP : self.formalCircuit.ProverAssumptions
      (self.formalCircuit.computedEnv hint (some w) Offset.start [1] []) (some w)) :
    self.Relation
      (((self.formalCircuit.main (some w)).operations Offset.start).compute hint
        ([1], [])).1.tail ∧
    self.formalCircuit.ProverSpec
      (self.formalCircuit.computedEnv hint (some w) Offset.start [1] []) (some w)
      (self.formalCircuit.output (some w) Offset.start) := by
  obtain ⟨i₂, a₂, hs⟩ := Operations.compute_extends hint
    ((self.formalCircuit.main (some w)).operations Offset.start) [1] []
  have hc := self.formalCircuit.complete_computed hint (some w) Offset.start [1] [] rfl rfl rfl
    trivial (by rw [self.assumptions_eq]; trivial) hP
  refine ⟨?_, hc.2⟩
  -- the prover's inputs reach the offset the circuit walks to, which is the key's
  have hlen : (([1] : List F) ++ i₂).length
      = (((self.formalCircuit.main (some w)).operations Offset.start).advance
          Offset.start).input := by
    have h := congrArg Offset.input (Operations.compute_length hint
      ((self.formalCircuit.main (some w)).operations Offset.start) [1] [])
    rw [hs] at h
    exact h
  rw [self.formalCircuit.advance_eq, self.nextOffset_indep] at hlen
  have henv : withPublic i₂
      (self.formalCircuit.computedEnv hint (some w) Offset.start [1] []).aux
      = (self.formalCircuit.computedEnv hint (some w) Offset.start [1] []).toEnvironment := by
    simp only [withPublic, FormalCircuit.computedEnv, ProverEnvironment.ofLists, hs]
    rfl
  rw [hs]
  simp only [List.length_append, List.length_singleton] at hlen
  refine ⟨?_, (self.formalCircuit.computedEnv hint (some w) Offset.start [1] []).aux, ?_⟩
  · simp only [List.singleton_append, List.tail_cons, numInputs]
    omega
  · simp only [List.singleton_append, List.tail_cons]
    rw [henv]
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · rw [← self.rows_indep (some w)] at hr
      exact hc.1 r hr
    · exact extraRows_holds _ _ r hr

end TopLevelCircuit

/-- A formal circuit over captured data whose rows, output and next offset do not depend on that
data. A parent proves it from its children's, through calls. -/
structure FormalCircuit.Indep {W γ : Type} [HasBelow γ] (G : FormalCircuit F (Option W) γ) :
    Prop where
  rows : ∀ w w' o, G.rowsAt w o = G.rowsAt w' o
  output : ∀ w w' o, G.output w o = G.output w' o
  nextOffset : ∀ w w' o, G.nextOffset w o = G.nextOffset w' o

end Bellman
