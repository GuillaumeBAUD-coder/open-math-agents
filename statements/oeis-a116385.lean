import Mathlib

/-!
# A116385: Expansion of e.g.f. Bessel_I(2,2x) + 2*Bessel_I(3,2x) + Bessel_I(4,2x).

Source: https://oeis.org/A116385
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A116385 (R. J. Mathar, Jun 13 2014):
(n+4)*a(n) -2*a(n-1) +(-7*n-8)*a(n-2) +6*a(n-3) +12*(n-2)*a(n-4)=0.

Conventions:
* The sequence has offset 0 (data 0, 0, 1, 2, 5, 10, 21, 42, 84, 168, 330, ...) and a(n) is n!
  times the coefficient of x^n in the exponential generating function
  Bessel_I(2,2x) + 2*Bessel_I(3,2x) + Bessel_I(4,2x).
* Bessel_I(v,z) is the modified Bessel function of the first kind, with the power series
  Bessel_I(v,z) = Sum_{k>=0} (z/2)^(2k+v) / (k! * (k+v)!). Hence
  Bessel_I(v,2x) = Sum_{k>=0} x^(2k+v) / (k! * (k+v)!).
  `i2 n`, `i3 n` and `i4 n` below are the coefficients of x^n in Bessel_I(2,2x),
  Bessel_I(3,2x) and Bessel_I(4,2x): `i2 n` is 1 / (((n-2)/2)! * ((n+2)/2)!) for even n >= 2,
  `i3 n` is 1 / (((n-3)/2)! * ((n+3)/2)!) for odd n >= 3, `i4 n` is
  1 / (((n-4)/2)! * ((n+4)/2)!) for even n >= 4, and they are 0 otherwise. The lower bounds
  on n are stated explicitly because subtraction of natural numbers is truncated.
* a(n) is defined as a rational number (it is an integer).
* The source gives no range for n. The recurrence is asserted for every `n ≥ 4`, which is
  exactly the range in which all the indices n, n-1, ..., n-4 are at least the offset 0.
* The identity is stated in `ℚ`, with the natural number `n` cast to `ℚ`, so the polynomial
  coefficients are exact.
-/

namespace OMA.S_oeis_a116385

/-- The coefficient of x^n in Bessel_I(2,2x) = Sum_{k>=0} x^(2k+2) / (k!*(k+2)!). -/
def i2 (n : ℕ) : ℚ :=
  if Even n ∧ 2 ≤ n then
    1 / ((((n - 2) / 2).factorial : ℚ) * (((n + 2) / 2).factorial : ℚ))
  else 0

/-- The coefficient of x^n in Bessel_I(3,2x) = Sum_{k>=0} x^(2k+3) / (k!*(k+3)!). -/
def i3 (n : ℕ) : ℚ :=
  if Odd n ∧ 3 ≤ n then
    1 / ((((n - 3) / 2).factorial : ℚ) * (((n + 3) / 2).factorial : ℚ))
  else 0

/-- The coefficient of x^n in Bessel_I(4,2x) = Sum_{k>=0} x^(2k+4) / (k!*(k+4)!). -/
def i4 (n : ℕ) : ℚ :=
  if Even n ∧ 4 ≤ n then
    1 / ((((n - 4) / 2).factorial : ℚ) * (((n + 4) / 2).factorial : ℚ))
  else 0

/-- A116385 (offset 0): n! times the coefficient of x^n in
Bessel_I(2,2x) + 2*Bessel_I(3,2x) + Bessel_I(4,2x). -/
def a (n : ℕ) : ℚ := (n.factorial : ℚ) * (i2 n + 2 * i3 n + i4 n)

/-- For every `n ≥ 4`,
(n+4)*a(n) - 2*a(n-1) + (-7*n-8)*a(n-2) + 6*a(n-3) + 12*(n-2)*a(n-4) = 0. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 4) * a n - 2 * a (n - 1) + (-7 * (n : ℚ) - 8) * a (n - 2) + 6 * a (n - 3)
      + 12 * ((n : ℚ) - 2) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a116385
