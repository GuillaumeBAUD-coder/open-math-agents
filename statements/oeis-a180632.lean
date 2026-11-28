import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Basic

open scoped BigOperators

namespace OMA.S_oeis_a180632

/-- A list `w` over `Fin n` is a superpermutation if every permutation `σ : Equiv.Perm (Fin n)`
appears as a contiguous sublist of `w`. -/
def IsSuperperm (n : ℕ) (w : List (Fin n)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n),
    ∃ i : ℕ, i + n ≤ w.length ∧ ∀ j : Fin n, w[i + j.val]? = some (σ j)

/-- OEIS A007489: `∑_{k=1}^n k!`. -/
def a007489 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, k.factorial

/-- OEIS A180632 conjecture: for every `n ≥ 1`, the minimum length of a superpermutation
of `Fin n` equals `A007489(n) = ∑_{k=1}^n k!`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (∃ w : List (Fin n), IsSuperperm n w ∧ w.length = a007489 n) ∧
      (∀ w : List (Fin n), IsSuperperm n w → a007489 n ≤ w.length) := by
  sorry

end OMA.S_oeis_a180632
