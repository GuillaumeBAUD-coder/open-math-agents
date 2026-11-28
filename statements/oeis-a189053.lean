import Mathlib

/-!
# A189053: Mathar's recurrence

Source: https://oeis.org/A189053
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A189053 (offset 0): expansion of d/dx log(1/(1-x/sqrt(1-4*x^2)));
data 1, 1, 7, 9, 41, 61, 225, 369, 1195, 2101, 6227, 11529, ...

Conjecture (R. J. Mathar, Jun 14 2016):
n*a(n) +(n-1)*a(n-1) +(-13*n+12)*a(n-2) +(-13*n+25)*a(n-3) +4*(14*n-27) *a(n-4)
+4*(14*n-41)*a(n-5) +80*(-n+3)*a(n-6) +80*(-n+4)*a(n-7) = 0.

Formalization: The entry gives the g.f. in closed form, sqrt(1-4*x^2)/(16*x^4+sqrt(1-4*x^2)*(4*x^3-x)-8*x^2+1), and this
closed form is used as the definition here. S is the formal power series over ℚ with S^2 = 1-4*x^2 and
constant term 1 (the constant term selects the branch of the square root), and G is determined by
(16*x^4 - 8*x^2 + 1 + (4*x^3 - x)*S)*G = S;
a(n) = [x^n] G. The recurrence involves a(n-7), so it is stated for n ≥ 7; it is checked by the data, for
example at n = 7: (7)*(369) + (6)*(225) + (-79)*(61) + (-66)*(41) + (284)*(9) + (228)*(7) + (-320)*(1) + (-240)*(1) = 0.
-/

namespace OMA.S_oeis_a189053

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A189053, for n ≥ 7. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X ^ 2 →
    coeff 0 S = 1 →
    (16 * X ^ 4 - 8 * X ^ 2 + 1 + (4 * X ^ 3 - X) * S) * G = S →
    ∀ n : ℕ, 7 ≤ n →
      ((n : ℚ)) * coeff n G + (-1 + (n : ℚ)) * coeff (n - 1) G +
        (12 - 13 * (n : ℚ)) * coeff (n - 2) G + (25 - 13 * (n : ℚ)) * coeff (n - 3) G +
        (-108 + 56 * (n : ℚ)) * coeff (n - 4) G + (-164 + 56 * (n : ℚ)) * coeff (n - 5) G +
        (240 - 80 * (n : ℚ)) * coeff (n - 6) G + (320 - 80 * (n : ℚ)) * coeff (n - 7) G = 0 := by
  sorry

end OMA.S_oeis_a189053
