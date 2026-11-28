import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a108625

/-- OEIS A108625: square array `T(n, k)` whose row `n` is the crystal ball sequence
for the `A_n` lattice, given by `T(n, k) = ∑_{i=0}^{k} C(n, i)^2 * C(n + k - i, k - i)`. -/
def a108625 (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), Nat.choose n i ^ 2 * Nat.choose (n + k - i) (k - i)

/-- OEIS A108625 conjecture (Peter Bala, Oct 12 2024):
For every positive integer `m` and every `n ≥ 0`,
`∑_{k=0}^{n} (-1)^(n + k) * C(n, k) * T(m * n, k) = ((m + 1) * n)! / (((m - 1) * n)! * (n!)^2)`,
written integrally as multiplying both sides by `((m - 1) * n)! * (n!)^2`. -/
theorem main :
    ∀ m n : ℕ, 1 ≤ m →
      (((m - 1) * n).factorial * n.factorial ^ 2 : ℤ) *
        (∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + k) * (Nat.choose n k : ℤ) * (a108625 (m * n) k : ℤ)) =
      (((m + 1) * n).factorial : ℤ) := by
  sorry

end OMA.S_oeis_a108625
