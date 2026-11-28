import Mathlib

/-!
# A351933: Expansion of e.g.f. exp(x / (1 - x^2/2)).

Source: https://oeis.org/A351933
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 1, 4, 13, 61, 331, 1996, 14449, ...
The entry gives the exponential generating function
  exp(x / (1 - x^2/2))
(the name of the entry). It is used here as the definition: a(n) is n! times the coefficient of x^n of that series,
where exp(u) is the exponential power series evaluated at the power series u (which has no constant
term). In normalised form the series is
  ((1)*exp((2*x)/(2 - x^2)) + (0)) / (1),
which is the expression used below. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Mar 09 2022) reads
  Conjecture D-finite with recurrence +4*a(n) -4*a(n-1) -4*(n-1)*(n-2)*a(n-2) -2*(n-1)*(n-2)*a(n-3) +(n-1)*(n-2)*(n-3)*(n-4)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a351933

open PowerSeries

/-- The exponent, a power series without constant term. -/
noncomputable def U : PowerSeries ℚ := (2 * X) * (2 - X ^ 2 : PowerSeries ℚ)⁻¹

/-- exp(U): the exponential series evaluated at U. -/
noncomputable def W : PowerSeries ℚ := (PowerSeries.exp ℚ).subst U

/-- A351933: n! times the coefficient of x^n in the exponential generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * coeff n
    (((1) * W + (0)) * (1 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A351933. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (4) * a n + (-4) * a (n - 1) + (-4 * (n : ℚ) ^ 2 + 12 * (n : ℚ) - 8) * a (n - 2)
      + (-2 * (n : ℚ) ^ 2 + 6 * (n : ℚ) - 4) * a (n - 3)
      + ((n : ℚ) ^ 4 - 10 * (n : ℚ) ^ 3 + 35 * (n : ℚ) ^ 2 - 50 * (n : ℚ) + 24) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a351933
