import Mathlib.Data.Nat.Notation

/-!
# bellman variables and linear combinations

The variables and linear combinations of a bellman 0.15.0 constraint system, as data, with
bellman's own operations on them.

A bellman linear combination is the list of its terms in the order they were added: nothing
merges repeated variables or drops zero coefficients when a term is added. The operations below
reproduce that list term for term, so that a constraint system built in Lean can be compared
with one exported from bellman by equality.

Everything lives in namespace `Bellman`: Clean defines its own `Variable` at the root.

Rust references (bellman 0.15.0):
- `src/lib.rs` — `Variable`, `Index`, `LinearCombination` and its `Add`/`Sub` impls,
  `ConstraintSystem::one`
-/

namespace Bellman

/-- A variable's index: input `i` (public, with input `0` the constant one) or auxiliary `j`
(private). Ports bellman `Index` (`lib.rs:180-186`). -/
inductive Index where
  | input (i : ℕ)
  | aux (j : ℕ)
deriving DecidableEq, Repr

/-- A variable of the constraint system, identified by its index. Ports bellman `Variable`
(`lib.rs:162-178`). -/
structure Variable where
  index : Index
deriving DecidableEq, Repr

/-- The constant-one variable, input `0`. Ports `ConstraintSystem::one` (`lib.rs:380-383`). -/
def one : Variable := ⟨.input 0⟩

/-- A linear combination: its terms `(variable, coefficient)`, in the order they were added.
Ports bellman `LinearCombination` (`lib.rs:188-191`). -/
structure LinearCombination (F : Type) where
  terms : List (Variable × F)
deriving DecidableEq, Repr

namespace LinearCombination

variable {F : Type}

/-- The empty linear combination. Ports `LinearCombination::zero` (`lib.rs:199-203`). -/
def zero : LinearCombination F := ⟨[]⟩

/-- `lc + (coeff, var)` appends the term `(var, coeff)`. Ports `Add<(Scalar, Variable)>`
(`lib.rs:205-213`). -/
def addTerm (lc : LinearCombination F) (coeff : F) (var : Variable) : LinearCombination F :=
  ⟨lc.terms ++ [(var, coeff)]⟩

/-- `lc + &other` adds `other`'s terms one by one, in order. Ports
`Add<&LinearCombination>` (`lib.rs:240-250`). -/
def addLC (lc other : LinearCombination F) : LinearCombination F :=
  other.terms.foldl (fun acc t => acc.addTerm t.2 t.1) lc

variable [Mul F] [Neg F] [One F]

/-- `lc - (coeff, var)` appends `(var, -coeff)`. Ports `Sub<(Scalar, Variable)>`
(`lib.rs:215-222`). -/
def subTerm (lc : LinearCombination F) (coeff : F) (var : Variable) : LinearCombination F :=
  lc.addTerm (-coeff) var

/-- `lc - &other` subtracts `other`'s terms one by one, in order. Ports
`Sub<&LinearCombination>` (`lib.rs:252-262`). -/
def subLC (lc other : LinearCombination F) : LinearCombination F :=
  other.terms.foldl (fun acc t => acc.subTerm t.2 t.1) lc

/-- `lc + (coeff, &other)` adds each term of `other` with its coefficient multiplied by
`coeff`, in order. Ports `Add<(Scalar, &LinearCombination)>` (`lib.rs:264-281`). -/
def addScaled (lc : LinearCombination F) (coeff : F) (other : LinearCombination F) :
    LinearCombination F :=
  other.terms.foldl (fun acc t => acc.addTerm (t.2 * coeff) t.1) lc

/-- `lc - (coeff, &other)` subtracts each term of `other` with its coefficient multiplied by
`coeff`, in order. Ports `Sub<(Scalar, &LinearCombination)>` (`lib.rs:283-300`). -/
def subScaled (lc : LinearCombination F) (coeff : F) (other : LinearCombination F) :
    LinearCombination F :=
  other.terms.foldl (fun acc t => acc.subTerm (t.2 * coeff) t.1) lc

/-! The operators `lc + (coeff, var)`, `lc + var`, `lc + &other`, `lc + (coeff, &other)` and
their `-` forms, one instance per bellman `Add`/`Sub` impl (`lib.rs:205-300`). `lc + var` is
`lc + (1, var)`; a borrowed `&other` is passed by value. -/

instance : HAdd (LinearCombination F) (F × Variable) (LinearCombination F) where
  hAdd lc t := lc.addTerm t.1 t.2
instance : HSub (LinearCombination F) (F × Variable) (LinearCombination F) where
  hSub lc t := lc.subTerm t.1 t.2
instance : HAdd (LinearCombination F) Variable (LinearCombination F) where
  hAdd lc v := lc.addTerm 1 v
instance : HSub (LinearCombination F) Variable (LinearCombination F) where
  hSub lc v := lc.subTerm 1 v
instance : HAdd (LinearCombination F) (LinearCombination F) (LinearCombination F) where
  hAdd := addLC
instance : HSub (LinearCombination F) (LinearCombination F) (LinearCombination F) where
  hSub := subLC
instance : HAdd (LinearCombination F) (F × LinearCombination F) (LinearCombination F) where
  hAdd lc t := lc.addScaled t.1 t.2
instance : HSub (LinearCombination F) (F × LinearCombination F) (LinearCombination F) where
  hSub lc t := lc.subScaled t.1 t.2

end LinearCombination

end Bellman
