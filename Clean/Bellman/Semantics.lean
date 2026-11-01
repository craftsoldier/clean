import Clean.Bellman.Basic
import Clean.Circuit.Basic

/-!
# The meaning of a bellman constraint system

When an assignment of values to a circuit's variables satisfies its constraints
(`Constraints`), and when it is honest: every allocated variable holds the value of its witness
function (`ExtendsWitnesses`). A gadget's soundness assumes the first, its completeness the
second.

## Constraints

An enforced constraint `A · B = C` holds when the values of its linear combinations satisfy
that equation; `Constraints env ops` says every constraint in `ops` holds. This is the
constraint relation of Groth, *On the Size of Pairing-based Non-interactive Arguments* (2016),
§2.3, whose equations range over `a₀ = 1` and the remaining variables; bellman's satisfaction
check computes the same. Allocations and namespace markers impose nothing. The constant-one
variable is input `0`; that it holds `1` is an assumption on the environment, made where it is
needed, not part of `Constraints`.

## Honest assignments

`ExtendsWitnesses env ops o` says each variable `ops` allocates, from offset `o`, holds the
value its witness function computes from `env`. It is a fixed-point condition on `env`: the
groth16 prover instead builds the assignment step by step, running each witness closure at
its allocation. The two agree when each witness function reads only variables allocated
before it; that is not enforced here.

## Normal forms

Reads of a variable stay folded as `env.get v` for an abstract `v`; a known variable reduces
to `env.input i` or `env.aux j`. A linear combination's value is the sum of coefficient ×
value over its terms, so that `circuit_norm` reduces the ±1 coefficients bellman emits to
plain sums and differences, and adding a whole linear combination, scaled or not, adds its
value.

## Rust references (bellman 0.15.0, groth16 0.2.0)

- `src/gadgets/test/mod.rs` — `eval_lc`, `TestConstraintSystem::which_is_unsatisfied`
- groth16 `src/prover.rs` — `eval`, `ProvingAssignment::alloc` and `alloc_input`
-/

namespace Bellman

variable {F : Type}

/-! ### Reading variables -/

/-! A `ProverEnvironment` is read as its `Environment`, as Clean's own environments are. -/

instance : Coe (ProverEnvironment F) (Environment F) := ⟨ProverEnvironment.toEnvironment⟩
instance : CoeOut (ProverEnvironment F) (Environment F) := ⟨ProverEnvironment.toEnvironment⟩

/-- The value an assignment gives a variable. -/
def Environment.get (env : Environment F) : Variable → F
  | ⟨.input i⟩ => env.input i
  | ⟨.aux j⟩ => env.aux j

@[circuit_norm]
theorem Environment.get_input (env : Environment F) (i : ℕ) :
    env.get ⟨.input i⟩ = env.input i := rfl

@[circuit_norm]
theorem Environment.get_aux (env : Environment F) (j : ℕ) : env.get ⟨.aux j⟩ = env.aux j :=
  rfl

@[circuit_norm]
theorem Environment.get_one (env : Environment F) : env.get one = env.input 0 := rfl

@[circuit_norm]
theorem Offset.start_input : Offset.start.input = 1 := rfl

@[circuit_norm]
theorem Offset.start_aux : Offset.start.aux = 0 := rfl

section Ring
variable [Ring F]

/-! ### Linear combinations -/

/-- The value of a list of terms: the sum of coefficient × value. -/
def LinearCombination.evalTerms (env : Environment F) : List (Variable × F) → F
  | [] => 0
  | (v, c) :: ts => c * env.get v + evalTerms env ts

/-- The value of a linear combination: the sum, over its terms, of the coefficient times the
variable's value. bellman's `eval_lc` multiplies value × coefficient (`test/mod.rs:124-142`),
the same in a commutative field; the groth16 prover's `eval` also skips zero coefficients
(`prover.rs:19-55`), which leaves the sum unchanged. -/
def LinearCombination.eval (env : Environment F) (lc : LinearCombination F) : F :=
  evalTerms env lc.terms

theorem LinearCombination.evalTerms_append (env : Environment F)
    (ts us : List (Variable × F)) :
    evalTerms env (ts ++ us) = evalTerms env ts + evalTerms env us := by
  induction ts with
  | nil => simp [evalTerms]
  | cons t ts ih => simp [evalTerms, ih, add_assoc]

@[circuit_norm]
theorem LinearCombination.eval_zero (env : Environment F) :
    (zero : LinearCombination F).eval env = 0 := rfl

theorem LinearCombination.eval_addTerm (env : Environment F) (lc : LinearCombination F) (c : F)
    (v : Variable) : (lc.addTerm c v).eval env = lc.eval env + c * env.get v := by
  simp [eval, addTerm, evalTerms_append, evalTerms]

@[circuit_norm]
theorem LinearCombination.eval_add_var (env : Environment F) (lc : LinearCombination F)
    (v : Variable) : (lc + v).eval env = lc.eval env + env.get v := by
  -- `lc + v` is `lc.addTerm 1 v`
  show (lc.addTerm 1 v).eval env = _
  rw [eval_addTerm, one_mul]

@[circuit_norm]
theorem LinearCombination.eval_sub_var (env : Environment F) (lc : LinearCombination F)
    (v : Variable) : (lc - v).eval env = lc.eval env - env.get v := by
  -- `lc - v` is `lc.addTerm (-1) v`
  show (lc.addTerm (-1) v).eval env = _
  rw [eval_addTerm, neg_one_mul, ← sub_eq_add_neg]

@[circuit_norm]
theorem LinearCombination.eval_add_term (env : Environment F) (lc : LinearCombination F)
    (c : F) (v : Variable) : (lc + (c, v)).eval env = lc.eval env + c * env.get v :=
  eval_addTerm env lc c v

@[circuit_norm]
theorem LinearCombination.eval_sub_term (env : Environment F) (lc : LinearCombination F)
    (c : F) (v : Variable) : (lc - (c, v)).eval env = lc.eval env - c * env.get v := by
  -- `lc - (c, v)` is `lc.addTerm (-c) v`
  show (lc.addTerm (-c) v).eval env = _
  rw [eval_addTerm, neg_mul, ← sub_eq_add_neg]

/-- Adding terms one by one, each coefficient mapped by `g`, adds the value of the mapped
terms. -/
theorem LinearCombination.eval_foldl_addTerm (env : Environment F) (g : F → F) :
    ∀ (ts : List (Variable × F)) (lc : LinearCombination F),
      (ts.foldl (fun acc t => acc.addTerm (g t.2) t.1) lc).eval env
        = lc.eval env + evalTerms env (ts.map fun t => (t.1, g t.2))
  | [], lc => by simp [evalTerms]
  | t :: ts, lc => by
    rw [List.foldl_cons, eval_foldl_addTerm env g ts, eval_addTerm]
    simp [evalTerms, add_assoc]

@[circuit_norm]
theorem LinearCombination.eval_add_lc (env : Environment F) (lc other : LinearCombination F) :
    (lc + other).eval env = lc.eval env + other.eval env := by
  -- `lc + other` adds `other`'s terms one by one
  show (other.terms.foldl (fun acc t => acc.addTerm (id t.2) t.1) lc).eval env = _
  rw [eval_foldl_addTerm]; simp [LinearCombination.eval]

theorem LinearCombination.evalTerms_map_neg (env : Environment F) :
    ∀ ts : List (Variable × F),
      evalTerms env (ts.map fun t => (t.1, -t.2)) = -evalTerms env ts
  | [] => by simp [evalTerms]
  | (v, c) :: ts => by
    simp only [List.map_cons, evalTerms, evalTerms_map_neg env ts, neg_mul, neg_add]

@[circuit_norm]
theorem LinearCombination.eval_sub_lc (env : Environment F) (lc other : LinearCombination F) :
    (lc - other).eval env = lc.eval env - other.eval env := by
  -- `lc - other` adds `other`'s terms one by one, negated
  show (other.terms.foldl (fun acc t => acc.addTerm (-t.2) t.1) lc).eval env = _
  rw [eval_foldl_addTerm, evalTerms_map_neg, ← sub_eq_add_neg]; rfl

/-! ### Constraints -/

/-- A constraint holds: `A · B = C` on the values of its linear combinations, the form of the
equations in Groth (2016), §2.3. bellman's satisfaction check computes the same
(`TestConstraintSystem::which_is_unsatisfied`, `test/mod.rs:255-269`). -/
def Constraint.Holds (env : Environment F) (r : Constraint F) : Prop :=
  r.a.eval env * r.b.eval env = r.c.eval env

@[circuit_norm]
theorem Constraint.holds_def (env : Environment F) (r : Constraint F) :
    r.Holds env = (r.a.eval env * r.b.eval env = r.c.eval env) := rfl

instance [DecidableEq F] (env : Environment F) (r : Constraint F) : Decidable (r.Holds env) :=
  inferInstanceAs (Decidable (_ = _))

/-- What one operation imposes: an enforced constraint holds; allocations and namespace
markers impose nothing. -/
def Operation.Constraints (env : Environment F) : Operation F → Prop
  | .alloc _ _ => True
  | .allocInput _ _ => True
  | .enforce _ r => r.Holds env
  | .pushNamespace _ => True
  | .popNamespace => True

/-- Every constraint in the operations holds. -/
def Constraints (env : Environment F) : Operations F → Prop
  | [] => True
  | op :: ops => op.Constraints env ∧ Constraints env ops

@[circuit_norm]
theorem constraints_nil (env : Environment F) : Constraints env ([] : Operations F) = True :=
  rfl

@[circuit_norm]
theorem constraints_cons (env : Environment F) (op : Operation F) (ops : Operations F) :
    Constraints env (op :: ops) = (op.Constraints env ∧ Constraints env ops) := rfl

@[circuit_norm]
theorem Operation.constraints_alloc (env : Environment F) (name : String)
    (compute : ProverEnvironment F → F) : (alloc name compute).Constraints env = True := rfl

@[circuit_norm]
theorem Operation.constraints_allocInput (env : Environment F) (name : String)
    (compute : ProverEnvironment F → F) : (allocInput name compute).Constraints env = True :=
  rfl

@[circuit_norm]
theorem Operation.constraints_enforce (env : Environment F) (name : String) (r : Constraint F) :
    (enforce name r).Constraints env = r.Holds env := rfl

@[circuit_norm]
theorem Operation.constraints_pushNamespace (env : Environment F) (name : String) :
    (pushNamespace name : Operation F).Constraints env = True := rfl

@[circuit_norm]
theorem Operation.constraints_popNamespace (env : Environment F) :
    (popNamespace : Operation F).Constraints env = True := rfl

instance [DecidableEq F] (env : Environment F) : (op : Operation F) →
    Decidable (op.Constraints env)
  | .alloc _ _ => isTrue trivial
  | .allocInput _ _ => isTrue trivial
  | .enforce _ r => inferInstanceAs (Decidable (r.Holds env))
  | .pushNamespace _ => isTrue trivial
  | .popNamespace => isTrue trivial

/-- `Constraints` is decidable when equality in `F` is. -/
def Constraints.decidable [DecidableEq F] (env : Environment F) :
    (ops : Operations F) → Decidable (Constraints env ops)
  | [] => isTrue trivial
  | op :: ops =>
    have : Decidable (Constraints env ops) := Constraints.decidable env ops
    inferInstanceAs (Decidable (op.Constraints env ∧ Constraints env ops))

instance [DecidableEq F] (env : Environment F) (ops : Operations F) :
    Decidable (Constraints env ops) := Constraints.decidable env ops

/-- The operations' constraints hold exactly when every constraint read off them holds: the
link between a circuit's operations and the rows of its constraint system. -/
theorem constraints_iff_forall_mem (env : Environment F) (ops : Operations F) :
    Constraints env ops ↔ ∀ r ∈ ops.constraints, r.Holds env := by
  induction ops with
  | nil => simp [Constraints, Operations.constraints]
  | cons op ops ih =>
    cases op <;> simp [Constraints, Operation.Constraints, Operations.constraints, ih]

end Ring

/-! ### Scaled linear combinations

bellman's `Add<(Scalar, &LinearCombination)>` multiplies each of `other`'s
coefficients by `coeff` on the right, so the value of `lc + (coeff, &other)` adds `coeff` times
`other`'s only in a commutative ring. -/

section CommRing
variable [CommRing F]

theorem LinearCombination.evalTerms_map_mul (env : Environment F) (c : F) :
    ∀ ts : List (Variable × F),
      evalTerms env (ts.map fun t => (t.1, t.2 * c)) = c * evalTerms env ts
  | [] => by simp [evalTerms]
  | (v, d) :: ts => by
    simp only [List.map_cons, evalTerms, evalTerms_map_mul env c ts, mul_add]
    rw [mul_comm d c, mul_assoc]

@[circuit_norm]
theorem LinearCombination.eval_add_scaled (env : Environment F) (lc : LinearCombination F)
    (c : F) (other : LinearCombination F) :
    (lc + (c, other)).eval env = lc.eval env + c * other.eval env := by
  show (other.terms.foldl (fun acc t => acc.addTerm (t.2 * c) t.1) lc).eval env = _
  rw [eval_foldl_addTerm (g := fun d => d * c), evalTerms_map_mul]; rfl

@[circuit_norm]
theorem LinearCombination.eval_sub_scaled (env : Environment F) (lc : LinearCombination F)
    (c : F) (other : LinearCombination F) :
    (lc - (c, other)).eval env = lc.eval env - c * other.eval env := by
  show (other.terms.foldl (fun acc t => acc.addTerm (-(t.2 * c)) t.1) lc).eval env = _
  -- `-(d * c) = d * -c`, so this is `lc + (-c, other)`
  have hm : (other.terms.map fun t => (t.1, -(t.2 * c)))
      = other.terms.map fun t => (t.1, t.2 * -c) := by simp [mul_neg]
  rw [eval_foldl_addTerm (g := fun d => -(d * c)), hm, evalTerms_map_mul, sub_eq_add_neg,
    neg_mul]; rfl

end CommRing

/-! ### Honest assignments -/

/-- The offset after one operation: an allocation takes the next auxiliary variable or the
next input, as `alloc` and `allocInput` do; the other operations allocate nothing. -/
def Operation.advance (o : Offset) : Operation F → Offset
  | .alloc _ _ => { o with aux := o.aux + 1 }
  | .allocInput _ _ => { o with input := o.input + 1 }
  | .enforce _ _ => o
  | .pushNamespace _ => o
  | .popNamespace => o

/-- What one operation, at offset `o`, requires of an honest assignment: an allocated
variable holds its witness function's value on the same environment, as the groth16 prover
pushes `f()` at each allocation (`prover.rs:76-103`). -/
def Operation.ExtendsWitness (env : ProverEnvironment F) (o : Offset) : Operation F → Prop
  | .alloc _ compute => env.aux o.aux = compute env
  | .allocInput _ compute => env.input o.input = compute env
  | .enforce _ _ => True
  | .pushNamespace _ => True
  | .popNamespace => True

/-- Every variable the operations allocate, from offset `o`, holds its witness function's
value on `env` — a fixed-point condition (see the module docstring). -/
def ExtendsWitnesses (env : ProverEnvironment F) : Operations F → Offset → Prop
  | [], _ => True
  | op :: ops, o => op.ExtendsWitness env o ∧ ExtendsWitnesses env ops (op.advance o)

@[circuit_norm]
theorem extendsWitnesses_nil (env : ProverEnvironment F) (o : Offset) :
    ExtendsWitnesses env ([] : Operations F) o = True := rfl

@[circuit_norm]
theorem extendsWitnesses_cons (env : ProverEnvironment F) (op : Operation F)
    (ops : Operations F) (o : Offset) :
    ExtendsWitnesses env (op :: ops) o
      = (op.ExtendsWitness env o ∧ ExtendsWitnesses env ops (op.advance o)) := rfl

@[circuit_norm]
theorem Operation.extendsWitness_alloc (env : ProverEnvironment F) (o : Offset) (name : String)
    (compute : ProverEnvironment F → F) :
    (alloc name compute).ExtendsWitness env o = (env.aux o.aux = compute env) := rfl

@[circuit_norm]
theorem Operation.extendsWitness_allocInput (env : ProverEnvironment F) (o : Offset)
    (name : String) (compute : ProverEnvironment F → F) :
    (allocInput name compute).ExtendsWitness env o = (env.input o.input = compute env) := rfl

@[circuit_norm]
theorem Operation.extendsWitness_enforce (env : ProverEnvironment F) (o : Offset)
    (name : String) (r : Constraint F) : (enforce name r).ExtendsWitness env o = True := rfl

@[circuit_norm]
theorem Operation.extendsWitness_pushNamespace (env : ProverEnvironment F) (o : Offset)
    (name : String) : (pushNamespace name : Operation F).ExtendsWitness env o = True := rfl

@[circuit_norm]
theorem Operation.extendsWitness_popNamespace (env : ProverEnvironment F) (o : Offset) :
    (popNamespace : Operation F).ExtendsWitness env o = True := rfl

@[circuit_norm]
theorem Operation.advance_alloc (o : Offset) (name : String)
    (compute : ProverEnvironment F → F) :
    (alloc name compute).advance o = { o with aux := o.aux + 1 } := rfl

@[circuit_norm]
theorem Operation.advance_allocInput (o : Offset) (name : String)
    (compute : ProverEnvironment F → F) :
    (allocInput name compute).advance o = { o with input := o.input + 1 } := rfl

@[circuit_norm]
theorem Operation.advance_enforce (o : Offset) (name : String) (r : Constraint F) :
    (enforce name r).advance o = o := rfl

@[circuit_norm]
theorem Operation.advance_pushNamespace (o : Offset) (name : String) :
    (pushNamespace name : Operation F).advance o = o := rfl

@[circuit_norm]
theorem Operation.advance_popNamespace (o : Offset) :
    (popNamespace : Operation F).advance o = o := rfl

end Bellman
