import Mathlib

/-!
# A025166: Mathar's recurrence

Source: https://oeis.org/A025166
Credit: @ivillar

Status: known result. The entry records: Conjecture verified using the differential equation (4*x - 1)*y(x) + (4*x^2 -
4*x + 1)*y'(x) = 0 satisfied by the e.g.f. - Robert Israel, May 17 2026

A025166 (offset 0): expansion of e.g.f. -exp(-x/(1-2*x))/(1-2*x);
data -1, -1, -1, 7, 127, 1711, 23231, 334391, 5144063, 84149983, 1446872959, 25661798119, ...

Conjecture (R. J. Mathar, Feb 05 2013):
a(n) + (-4*n+3)*a(n-1) + 4*(n-1)^2*a(n-2) = 0.

Formalization: R is the formal power series over ℚ with R*(1-2*x) = -x, that is the exponent
(-x)/(1-2*x); it has zero constant term, so the composition exp(R) of the exponential series with R is
defined (`(PowerSeries.exp ℚ).subst R`). The e.g.f. F is determined by F*(1-2*x) = (-1)*exp(R), and
a(n) = n! [x^n] F. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the
data, for example at n = 2: (1)*(-1) + (-5)*(-1) + (4)*(-1) = 0.
-/

namespace OMA.S_oeis_a025166

open PowerSeries

/-- The sequence with exponential generating function F: a(n) = n! [x^n] F. -/
noncomputable def a (F : ℚ⟦X⟧) (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n F

/-- Mathar's conjectured recurrence for A025166, for n ≥ 2. -/
theorem main : ∀ R F : ℚ⟦X⟧, R * (1 - 2 * X) = -X →
    F * (1 - 2 * X) = (-1) * (PowerSeries.exp ℚ).subst R →
    ∀ n : ℕ, 2 ≤ n →
      (1) * a F n + (3 - 4 * (n : ℚ)) * a F (n - 1) +
        (4 - 8 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * a F (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a025166
