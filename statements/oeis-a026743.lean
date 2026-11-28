import Mathlib

/-!
# A026743: Mathar's recurrence

Source: https://oeis.org/A026743
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A026743 (offset 0): a(n) = Sum_{j=0..n} T(n,j), T given by A026736;
data 1, 2, 4, 8, 17, 34, 73, 146, 314, 628, 1350, 2700, ...

Conjecture (R. J. Mathar, Jan 13 2023): D-finite with recurrence
n*a(n) -2*a(n-1) +(-11*n+20)*a(n-2) +14*a(n-3) +(39*n-152)*a(n-4) -22*a(n-5) +(-41*n+268)*a(n-6)
-6*a(n-7) +12*(-n+6)*a(n-8) = 0.

Formalization: The entry gives the g.f. ((1-3*x^2)*sqrt((1+2*x)/(1-2*x)) + (1+2*x)*(1+x^2))/(2*(1 - 4*x^2 - x^4)) (David
Callan, Jan 17 2016), and this closed form is used as the definition here. R is the formal power
series over ℚ with (1-2*x)*R^2 = 1+2*x and constant term 1, that is R = sqrt((1+2x)/(1-2x)) (the constant
term selects the branch of the square root), and G is determined by
2*(1 - 4*x^2 - x^4)*G = (1-3*x^2)*R + (1+2*x)*(1+x^2);
a(n) = [x^n] G. The recurrence involves a(n-8), so it is stated for n ≥ 8; it is checked by the data, for
example at n = 8: (8)*(314) + (-2)*(146) + (-68)*(73) + (14)*(34) + (160)*(17) + (-22)*(8) + (-60)*(4) + (-6)*(2) + (-24)*(1) = 0.
-/

namespace OMA.S_oeis_a026743

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A026743, for n ≥ 8. -/
theorem main : ∀ R G : ℚ⟦X⟧, (1 - 2 * X) * R ^ 2 = 1 + 2 * X →
    coeff 0 R = 1 →
    2 * (1 - 4 * X ^ 2 - X ^ 4) * G = (1 - 3 * X ^ 2) * R + (1 + 2 * X) * (1 + X ^ 2) →
    ∀ n : ℕ, 8 ≤ n →
      ((n : ℚ)) * coeff n G + (-2) * coeff (n - 1) G +
        (20 - 11 * (n : ℚ)) * coeff (n - 2) G + (14) * coeff (n - 3) G +
        (-152 + 39 * (n : ℚ)) * coeff (n - 4) G + (-22) * coeff (n - 5) G +
        (268 - 41 * (n : ℚ)) * coeff (n - 6) G + (-6) * coeff (n - 7) G +
        (72 - 12 * (n : ℚ)) * coeff (n - 8) G = 0 := by
  sorry

end OMA.S_oeis_a026743
