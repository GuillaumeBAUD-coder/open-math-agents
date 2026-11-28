import Mathlib

/-!
# A103821: A Whitney transform of the central binomial coefficients A000984.

Source: https://oeis.org/A103821
Credit: @vivanpoddar

The sequence (offset 0) is 1, 3, 11, 43, 179, 771, 3395, 15171, 68515, 311907, ... The entry gives the
formula a(n) = Sum_{k=0..n} C(2*k, k)*Sum_{i=0..n} C(k, i-k), which is used here as the definition; a
binomial coefficient with negative lower index is 0, so the inner sum runs over k <= i <= n.

The conjecture (R. J. Mathar, Dec 14 2011) reads
n*a(n) + (2-5*n)*a(n-1) + 2*a(n-2) + 4*(n-1)*a(n-3) = 0.
It involves a(n-3), so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a103821

/-- A103821 (offset 0): a(n) = Sum_{k=0..n} C(2k, k) * Sum_{i=k..n} C(k, i-k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((2 * k).choose k : ℤ) * ∑ i ∈ Finset.Icc k n, (k.choose (i - k) : ℤ)

/-- Mathar's conjectured recurrence for A103821. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (n : ℤ) * a n + (2 - 5 * (n : ℤ)) * a (n - 1) + 2 * a (n - 2) + 4 * ((n : ℤ) - 1) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a103821
