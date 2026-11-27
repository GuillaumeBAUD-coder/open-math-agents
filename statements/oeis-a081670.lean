import Mathlib

/-!
# A081670: a(n) = 3^n-1+C(2n,n).

Source: https://oeis.org/A081670
Credit: @agchua

R. J. Mathar (Nov 12 2012), in the formula section of A081670:
  Conjecture: n*(3*n^2-17*n+26)*a(n) +2*(-12*n^3+71*n^2-131*n+60)*a(n-1)
  +(57*n^3-347*n^2+710*n-480)*a(n-2) -6*(2*n-5)*(3*n^2-11*n+12)*a(n-3) = 0.
The sequence has offset 0. The recurrence uses a(n-3), so the conjecture is stated for n ≥ 3.
C(2n,n) is the binomial coefficient (2n).choose n; terms are taken in ℤ.
-/

namespace OMA.S_oeis_a081670

/-- A081670(n) = 3^n - 1 + C(2n,n). -/
def a (n : ℕ) : ℤ := 3 ^ n - 1 + ((2 * n).choose n : ℤ)

/-- Mathar's conjecture: the order-3 recurrence holds for all n ≥ 3. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (n : ℤ) * (3 * (n : ℤ) ^ 2 - 17 * (n : ℤ) + 26) * a n
      + 2 * (-12 * (n : ℤ) ^ 3 + 71 * (n : ℤ) ^ 2 - 131 * (n : ℤ) + 60) * a (n - 1)
      + (57 * (n : ℤ) ^ 3 - 347 * (n : ℤ) ^ 2 + 710 * (n : ℤ) - 480) * a (n - 2)
      - 6 * (2 * (n : ℤ) - 5) * (3 * (n : ℤ) ^ 2 - 11 * (n : ℤ) + 12) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a081670
