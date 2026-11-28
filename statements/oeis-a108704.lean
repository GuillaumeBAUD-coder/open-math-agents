import Mathlib

/-!
# A108704: Mathar's recurrence

Source: https://oeis.org/A108704
Credit: @ivillar

Status: known result. The entry records that the exponential generating series A(t) satisfies the
differential equation (1-2*t)*A'(t) = (1+t-2*t^2)*A(t), which is equivalent to the conjectured
recurrence (Emanuele Munarini, May 25 2022).

A108704 (offset 0): number of partitions of 112233...nn into n pairs;
data 1, 1, 4, 18, 126, 1110, 12120, 156660, 2341500, 39701340, 752839920, 15785181720, ...

Conjecture (R. J. Mathar, Jun 08 2016):
a(n)-(2*n-1)*a(n-1)-(n-1)*a(n-2)+2*(n-1)*(n-2)*a(n-3) = 0.

Formalization: the entry gives the e.g.f. exp(x*x/2)/sqrt(1-2*x). S is the formal power series over ℚ
with S^2 = 1-2*x and constant term 1, that is S = sqrt(1-2x) (the constant term selects the branch of
the square root); R is the exponent x^2/2, given by 2*R = x^2; it has zero constant term, so the
composition exp(R) of the exponential series with R is defined (`(PowerSeries.exp ℚ).subst R`). The
e.g.f. F is determined by F*S = exp(R), and a(n) = n! [x^n] F. The recurrence involves a(n-3), so it
is stated for n ≥ 3; it is checked by the data, for example at n = 3:
(1)*(18) + (-5)*(4) + (-2)*(1) + (4)*(1) = 0.
-/

namespace OMA.S_oeis_a108704

open PowerSeries

/-- The sequence with exponential generating function F: a(n) = n! [x^n] F. -/
noncomputable def a (F : ℚ⟦X⟧) (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n F

/-- Mathar's conjectured recurrence for A108704, for n ≥ 3. -/
theorem main : ∀ S R F : ℚ⟦X⟧, S ^ 2 = 1 - 2 * X →
    coeff 0 S = 1 →
    2 * R = X ^ 2 →
    F * S = (PowerSeries.exp ℚ).subst R →
    ∀ n : ℕ, 3 ≤ n →
      a F n - (2 * (n : ℚ) - 1) * a F (n - 1) - ((n : ℚ) - 1) * a F (n - 2) +
        2 * ((n : ℚ) - 1) * ((n : ℚ) - 2) * a F (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a108704
