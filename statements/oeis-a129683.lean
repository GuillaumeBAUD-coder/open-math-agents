import Mathlib

/-!
# A129683: Mathar's recurrence

Source: https://oeis.org/A129683
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A129683 (offset 0): expansion of (1/(1-2x))*exp(2x/(1-2x));
data 1, 4, 28, 272, 3344, 49472, 852928, 16758016, 369082624, 8996922368, 240294124544, 6974172532736, ...

Conjecture (R. J. Mathar, Nov 14 2011):
a(n) -4*n*a(n-1) +4*(n-1)^2*a(n-2) = 0.

Formalization: R is the formal power series over ℚ with R*(1-2*x) = 2*x, that is the exponent
(2*x)/(1-2*x); it has zero constant term, so the composition exp(R) of the exponential series with R is
defined (`(PowerSeries.exp ℚ).subst R`). The e.g.f. F is determined by F*(1-2*x) = (1)*exp(R), and
a(n) = n! [x^n] F. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the
data, for example at n = 2: (1)*(28) + (-8)*(4) + (4)*(1) = 0.
-/

namespace OMA.S_oeis_a129683

open PowerSeries

/-- The sequence with exponential generating function F: a(n) = n! [x^n] F. -/
noncomputable def a (F : ℚ⟦X⟧) (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n F

/-- Mathar's conjectured recurrence for A129683, for n ≥ 2. -/
theorem main : ∀ R F : ℚ⟦X⟧, R * (1 - 2 * X) = 2 * X →
    F * (1 - 2 * X) = (1) * (PowerSeries.exp ℚ).subst R →
    ∀ n : ℕ, 2 ≤ n →
      (1) * a F n + (-4 * (n : ℚ)) * a F (n - 1) +
        (4 - 8 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * a F (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a129683
