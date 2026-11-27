import Mathlib

/-!
# A000579: Figurate numbers or binomial coefficients C(n, 6).

Source: https://oeis.org/A000579
Credit: @rabdelaal

OEIS A000579 records the conjecture that `a(n+3) = Sum_{0 <= k, L, m <= n;
k + L + m <= n} k*L*m`, where `a n = C(n, 6)`.
-/

namespace OMA.S_oeis_a000579

/-- The OEIS A000579 entry: the binomial coefficient `C(n, 6)`. -/
def a (n : ℕ) : ℕ := Nat.choose n 6

/-- The conjecture recorded in OEIS A000579: `C(n+3, 6)` equals the sum of `k*L*m`
over all `0 <= k, L, m` with `k + L + m <= n`. -/
theorem main : ∀ n : ℕ, a (n + 3) =
    ∑ k ∈ Finset.range (n + 1), ∑ L ∈ Finset.range (n + 1 - k),
      ∑ m ∈ Finset.range (n + 1 - k - L), k * L * m := by
  sorry

end OMA.S_oeis_a000579
