import Mathlib

/-!
# OEIS A234307: the alternating gcd sum

Peter Bala conjectured that the sum of gcds of the parts in the two-part
partitions of `2*n` is one quarter of the indicated alternating sum.

Source: https://oeis.org/A234307
Formalization: @senamakel
-/

namespace OMA.S_oeis_a234307

/-- The gcd sum over the pairs `(2*n-i,i)` for `1 ≤ i ≤ n`. -/
def term (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, Nat.gcd (2*n-i) i

theorem main : ∀ n : ℕ, 0 < n →
    4 * (term n : ℤ) =
      ∑ k ∈ Finset.Icc 1 (4*n), (-1 : ℤ)^k * (Nat.gcd k (8*n) : ℤ) := by
  sorry

end OMA.S_oeis_a234307
