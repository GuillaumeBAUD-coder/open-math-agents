import Mathlib

namespace OMA.S_mo_356488

open scoped BigOperators

/-- The sum of the remainders of b modulo 1 through ⌊(b−1)/2⌋. -/
def remainderSum (b : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 ((b - 1) / 2), b % k

/-- The signed sums in the question, with z(0) = 0. -/
def signedSum (m : ℕ) : ℤ :=
  ∑ n ∈ Finset.range m, (-1 : ℤ) ^ remainderSum (n + 1)

/-- Every positive-index sum is positive, and the sums are unbounded above. -/
theorem main :
    (∀ m : ℕ, 0 < m → 0 < signedSum m) ∧
    (∀ C : ℤ, ∃ m : ℕ, C < signedSum m) := by
  sorry

end OMA.S_mo_356488
