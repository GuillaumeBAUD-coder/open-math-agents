import Mathlib

/-!
# A039598: Catalan's triangle (odd-numbered columns of the Chebyshev U expansion triangle).

Source: https://oeis.org/A039598
Credit: @thatoneguy006

The conjecture stated here, from the entry (Werner Schulte):

  Conjecture: Sum_{k=0..n} T(n,k)/(k+1)^2 = H(n+1)*A000108(n)*(2*n+1)/(n+1),
  where H(n+1) = Sum_{k=0..n} 1/(k+1).

The entry adds that Maple's sum command can be used to verify this identity (Peter Bala,
Nov 25 2025); no proof is given there.

Definitions.
* `T n k` for `0 ≤ k ≤ n` is the closed form in the entry (Henry Bottomley):
  a(n, k) = C(2n+1, n-k)*2*(k+1)/(n+k+2). It is evaluated in ℚ, so the division is exact.
  Its rows are 1; 2, 1; 5, 4, 1; 14, 14, 6, 1; 42, 48, 27, 8, 1, the data of the entry. The
  statement only uses `T n k` with `k ≤ n`, the range of the triangle, where `n - k` is the
  ordinary difference.
* A000108 is Mathlib's `catalan`.
* H(n+1) is written out as in the source, `∑ k ∈ range (n + 1), 1 / (k + 1)`.
-/

namespace OMA.S_oeis_a039598

/-- The triangle A039598, `T(n, k) = C(2n+1, n-k) * 2(k+1) / (n+k+2)` for `0 ≤ k ≤ n`. -/
def T (n k : ℕ) : ℚ :=
  ((2 * n + 1).choose (n - k) : ℚ) * (2 * ((k : ℚ) + 1)) / ((n : ℚ) + k + 2)

/-- Schulte's conjecture. -/
theorem main : ∀ n : ℕ,
    ∑ k ∈ Finset.range (n + 1), T n k / ((k : ℚ) + 1) ^ 2 =
      (∑ k ∈ Finset.range (n + 1), (1 : ℚ) / ((k : ℚ) + 1)) * (catalan n : ℚ) *
        (2 * (n : ℚ) + 1) / ((n : ℚ) + 1) := by
  sorry

end OMA.S_oeis_a039598
