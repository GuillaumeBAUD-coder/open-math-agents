import Mathlib

/-!
# A171847: Mathar's recurrence

Source: https://oeis.org/A171847
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A171847 (offset 0): total area under all peakless Motzkin paths of length n (n>=0);
data 0, 0, 0, 2, 7, 22, 68, 198, 563, 1578, 4367, 11980, ...

Conjecture (R. J. Mathar, Jul 22 2022): D-finite with recurrence
(n+2)*a(n) +5*(-n-1)*a(n-1) +(7*n-4)*a(n-2) +2*(-3*n+7)*a(n-3) +(13*n-18)*a(n-4) +11*(-n+3)*a(n-5)
+(13*n-60)*a(n-6) +2*(-3*n+11)*a(n-7) +(7*n-38)*a(n-8) +5*(-n+7)*a(n-9) +(n-8)*a(n-10) = 0.

Formalization: T is the series g of the entry: the formal power series over ℚ with T = 1 + x*T + x^2*T*(T-1) (this
equation has exactly one power series solution, with constant term 1; it is the g.f. of the peakless
Motzkin paths); and the g.f. G is determined by
G*(1 + x + x^2)*(1 - 3*x + x^2) = x^2*(T^2 - 1);
a(n) = [x^n] G. The recurrence involves a(n-10), so it is stated for n ≥ 10; it is checked by the data, for
example at n = 10: (12)*(4367) + (-55)*(1578) + (66)*(563) + (-46)*(198) + (112)*(68) + (-77)*(22) + (70)*(7) + (-38)*(2) + (32)*(0) + (-15)*(0) + (2)*(0) = 0.
-/

namespace OMA.S_oeis_a171847

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A171847, for n ≥ 10. -/
theorem main : ∀ T G : ℚ⟦X⟧, T = 1 + X * T + X ^ 2 * T * (T - 1) →
    G * ((1 + X + X ^ 2) * (1 - 3 * X + X ^ 2)) = X ^ 2 * (T ^ 2 - 1) →
    ∀ n : ℕ, 10 ≤ n →
      (2 + (n : ℚ)) * coeff n G + (-5 - 5 * (n : ℚ)) * coeff (n - 1) G +
        (-4 + 7 * (n : ℚ)) * coeff (n - 2) G + (14 - 6 * (n : ℚ)) * coeff (n - 3) G +
        (-18 + 13 * (n : ℚ)) * coeff (n - 4) G + (33 - 11 * (n : ℚ)) * coeff (n - 5) G +
        (-60 + 13 * (n : ℚ)) * coeff (n - 6) G + (22 - 6 * (n : ℚ)) * coeff (n - 7) G +
        (-38 + 7 * (n : ℚ)) * coeff (n - 8) G + (35 - 5 * (n : ℚ)) * coeff (n - 9) G +
        (-8 + (n : ℚ)) * coeff (n - 10) G = 0 := by
  sorry

end OMA.S_oeis_a171847
