import Mathlib

/-!
# A243816: Mathar's recurrence

Source: https://oeis.org/A243816
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A243816 (offset 0): expansion of (x*sqrt(4*x^2+1)-x)/(x*sqrt(-(2*sqrt(4*x^2+1)-x-2)/x) + sqrt(4*x^2+1)-x-1);
data -1, 2, 0, 2, 5, 10, 27, 86, 264, 806, 2559, 8332, ...

Conjecture (R. J. Mathar, Jan 25 2020): D-finite with recurrence
2*n*(n-1)*(2*n-3)*a(n) -(n-1)*(47*n^2-221*n+260)*a(n-1) +4*(38*n^3-300*n^2+777*n-660)*a(n-2)
+4*(-94*n^3+1006*n^2-3617*n+4355)*a(n-3) +16*(n-5)*(64*n^2-510*n+1041)*a(n-4)
-16*(n-5)*(n-6)*(47*n-221)*a(n-5) +1920*(n-5)*(n-6)*(n-7)*a(n-6) = 0.

Formalization: T is the formal power series over ℚ with T^2 = 1+4*x^2 and constant term 1; U is the formal power
series with x*U^2 = 2*(1-T) + x and constant term 1, that is U = sqrt(2*(1 - sqrt(4x^2+1))/x + 1) (the
constant terms select the branches of the square roots); and G is determined by
G*(x*U + T - x - 1) = x*T - x; here -(2*sqrt(4x^2+1) - x - 2)/x = U^2 (its constant term is recorded
as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-6), so it is stated for n ≥ 6; it is checked by the data, for
example at n = 6: (540)*(27) + (-3130)*(10) + (5640)*(5) + (-5740)*(2) + (4560)*(0) + (0)*(2) + (0)*(-1) = 0.
-/

namespace OMA.S_oeis_a243816

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A243816, for n ≥ 6. -/
theorem main : ∀ T U G : ℚ⟦X⟧, T ^ 2 = 1 + 4 * X ^ 2 →
    coeff 0 T = 1 →
    X * U ^ 2 = 2 * (1 - T) + X →
    coeff 0 U = 1 →
    G * (X * U + T - X - 1) = X * T - X →
    coeff 0 G = -1 →
    ∀ n : ℕ, 6 ≤ n →
      (6 * (n : ℚ) - 10 * (n : ℚ) ^ 2 + 4 * (n : ℚ) ^ 3) * coeff n G + (260 - 481 * (n : ℚ) + 268 * (n : ℚ) ^ 2 - 47 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-2640 + 3108 * (n : ℚ) - 1200 * (n : ℚ) ^ 2 + 152 * (n : ℚ) ^ 3) * coeff (n - 2) G + (17420 - 14468 * (n : ℚ) + 4024 * (n : ℚ) ^ 2 - 376 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (-83280 + 57456 * (n : ℚ) - 13280 * (n : ℚ) ^ 2 + 1024 * (n : ℚ) ^ 3) * coeff (n - 4) G + (106080 - 61456 * (n : ℚ) + 11808 * (n : ℚ) ^ 2 - 752 * (n : ℚ) ^ 3) * coeff (n - 5) G +
        (-403200 + 205440 * (n : ℚ) - 34560 * (n : ℚ) ^ 2 + 1920 * (n : ℚ) ^ 3) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a243816
