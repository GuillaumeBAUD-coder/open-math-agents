import Mathlib

/-!
# A171851: Mathar's recurrence

Source: https://oeis.org/A171851
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A171851 (offset 0): the difference between the area under a peakless Motzkin path and the number of its U-steps, summed over all peakless Motzkin paths of length n (n>=0);
data 0, 0, 0, 1, 4, 14, 46, 140, 412, 1186, 3354, 9368, ...

Conjecture (R. J. Mathar, Jul 22 2022): D-finite with recurrence
-2*(n+2)*(1088*n-6417)*a(n) +(10968*n^2-55789*n-59252)*a(n-1) +2*(-6704*n^2+45808*n-27647)*a(n-2)
+2*(2264*n^2-18729*n+42256)*a(n-3) +2*(-11968*n^2+82555*n-88362)*a(n-4)
+(24904*n^2-243375*n+511724)*a(n-5) +4*(-1088*n^2+9137*n-25680)*a(n-6)
+2*(6616*n^2-65333*n+164938)*a(n-7) -2*(5616*n-25895)*(n-7)*a(n-8) +(2264*n-10805)*(n-8)*a(n-9) =
0.

Formalization: T is the series g of the entry: the formal power series over ℚ with T = 1 + x*T + x^2*T*(T-1) (this
equation has exactly one power series solution, with constant term 1; it is the g.f. of the peakless
Motzkin paths); and the g.f. G is determined by
G*(1 - x + x^2 - 2*x^2*T)^2 = x^3*T^2*(1 - 2*x + 2*x*T), the stated expression multiplied by its denominator;
a(n) = [x^n] G. The recurrence involves a(n-9), so it is stated for n ≥ 9; it is checked by the data, for
example at n = 9: (-74250)*(1186) + (327055)*(412) + (-316798)*(140) + (114158)*(46) + (-629550)*(14) + (338573)*(4) + (-126300)*(1) + (225674)*(0) + (-98596)*(0) + (9571)*(0) = 0.
-/

namespace OMA.S_oeis_a171851

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A171851, for n ≥ 9. -/
theorem main : ∀ T G : ℚ⟦X⟧, T = 1 + X * T + X ^ 2 * T * (T - 1) →
    G * (1 - X + X ^ 2 - 2 * X ^ 2 * T) ^ 2 = X ^ 3 * T ^ 2 * (1 - 2 * X + 2 * X * T) →
    ∀ n : ℕ, 9 ≤ n →
      (25668 + 8482 * (n : ℚ) - 2176 * (n : ℚ) ^ 2) * coeff n G + (-59252 - 55789 * (n : ℚ) + 10968 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-55294 + 91616 * (n : ℚ) - 13408 * (n : ℚ) ^ 2) * coeff (n - 2) G + (84512 - 37458 * (n : ℚ) + 4528 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-176724 + 165110 * (n : ℚ) - 23936 * (n : ℚ) ^ 2) * coeff (n - 4) G + (511724 - 243375 * (n : ℚ) + 24904 * (n : ℚ) ^ 2) * coeff (n - 5) G +
        (-102720 + 36548 * (n : ℚ) - 4352 * (n : ℚ) ^ 2) * coeff (n - 6) G + (329876 - 130666 * (n : ℚ) + 13232 * (n : ℚ) ^ 2) * coeff (n - 7) G +
        (-362530 + 130414 * (n : ℚ) - 11232 * (n : ℚ) ^ 2) * coeff (n - 8) G + (86440 - 28917 * (n : ℚ) + 2264 * (n : ℚ) ^ 2) * coeff (n - 9) G = 0 := by
  sorry

end OMA.S_oeis_a171851
