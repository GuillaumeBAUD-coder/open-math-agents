import Mathlib

/-!
# A024719: a(n) = (1/3)*(2 + Sum_{k=0..n} C(3k,k)).

Source: https://oeis.org/A024719
Credit: @marcelopierry

Conjecture (R. J. Mathar, Sep 29 2012, in the formulas of A024719):
2*n*(2*n-1)*a(n) + (-31*n^2 + 29*n - 6)*a(n-1) + 3*(3*n-1)*(3*n-2)*a(n-2) = 0.

Conventions:
* The sequence has offset 0 (data 1, 2, 7, 35, 200, 1201, ...); it is computed in the rationals
  (the values are integers).
* The recurrence involves a(n-2), so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a024719

/-- A024719(n) = (1/3)*(2 + Sum_{k=0..n} C(3k,k)). -/
def a (n : ℕ) : ℚ := (1 / 3) * (2 + ∑ k ∈ Finset.range (n + 1), ((3 * k).choose k : ℚ))

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    2 * (n : ℚ) * (2 * n - 1) * a n + (-31 * (n : ℚ) ^ 2 + 29 * n - 6) * a (n - 1) +
      3 * (3 * (n : ℚ) - 1) * (3 * n - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a024719
