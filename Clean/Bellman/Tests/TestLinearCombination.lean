import Clean.Bellman.LinearCombination
import Mathlib.Data.Int.Notation

/-!
Each bellman linear-combination operation appends exactly the terms bellman 0.15.0 appends, in
the same order, with no merging. The expected lists are read off bellman's `Add`/`Sub` impls
(`lib.rs:205-300`).
-/

namespace Bellman.Tests.TestLinearCombination
open Bellman LinearCombination

def a : Variable := ⟨.aux 0⟩
def b : Variable := ⟨.aux 1⟩
def x : Variable := ⟨.input 1⟩

-- `one` is input 0
example : one = ⟨.input 0⟩ := rfl

-- `lc + (c, v)` appends `(v, c)`; `lc - (c, v)` appends `(v, -c)`
example : ((zero : LinearCombination ℤ) + ((3 : ℤ), a)).terms = [(a, 3)] := rfl
example : ((zero : LinearCombination ℤ) - ((3 : ℤ), a)).terms = [(a, -3)] := rfl

-- `lc + v` is `lc + (1, v)`; `lc - v` is `lc - (1, v)`
-- (`AllocatedBit::alloc`'s first LC: `lc + CS::one() - var`)
example : ((zero : LinearCombination ℤ) + one - a).terms = [(one, 1), (a, -1)] := rfl

-- nothing merges: a repeated variable stays twice, a cancelling pair stays as two terms
example : ((zero : LinearCombination ℤ) + b + a - a + b).terms =
    [(b, 1), (a, 1), (a, -1), (b, 1)] := rfl

-- `lc + &other` appends `other`'s terms in order; `lc - &other` negates each
def other : LinearCombination ℤ := ⟨[(a, 2), (x, -5)]⟩
example : (((zero : LinearCombination ℤ) + b) + other).terms = [(b, 1), (a, 2), (x, -5)] := rfl
example : (((zero : LinearCombination ℤ) + b) - other).terms = [(b, 1), (a, -2), (x, 5)] := rfl

-- `lc + (c, &other)` multiplies each coefficient by `c`; `lc - (c, &other)` also negates
example : ((zero : LinearCombination ℤ) + ((3 : ℤ), other)).terms = [(a, 6), (x, -15)] := rfl
example : ((zero : LinearCombination ℤ) - ((3 : ℤ), other)).terms = [(a, -6), (x, 15)] := rfl

end Bellman.Tests.TestLinearCombination
