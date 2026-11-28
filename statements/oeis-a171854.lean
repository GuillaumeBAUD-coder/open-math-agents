import Mathlib

/-!
# A171854: Mathar's recurrence, corrected to n ≥ 7

Source: https://oeis.org/A171854
Credit: @ivillar

Status: false as stated at n = 6 (the left side is -7275 at n = 6 on the OEIS data); `main` is the
corrected recurrence (n ≥ 7), which is proved.

A171854 (offset 0): number of ladders in all peakless Motzkin paths of length n (n>=0);
data 0, 0, 0, 1, 3, 7, 19, 50, 129, 334, 862, 2220, ...

Conjecture (R. J. Mathar, Jul 22 2022): D-finite with recurrence
-(n+2)*(1390*n-8929)*a(n) +(4884*n^2-25542*n-20107)*a(n-1) +(60*n^2-6110*n-2249)*a(n-2)
+(-5080*n^2+49134*n-115735)*a(n-3) +(-8476*n^2+66210*n-98877)*a(n-4)
+(-3652*n^2+41338*n-109281)*a(n-5) +(2878*n-9993)*(n-7)*a(n-6) = 0.

Formalization: T is the series g of the entry: the formal power series over ℚ with T = 1 + x*T + x^2*T*(T-1) (this
equation has exactly one power series solution, with constant term 1; it is the g.f. of the peakless
Motzkin paths); and the g.f. G is determined by
G*(1 - x^2*T^2) = x^2*(1 - x^2)*T^2*(T-1), the stated expression multiplied by its denominator;
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 7): on the data the left side of the recurrence as
stated is -7275 at n = 6, and it vanishes from n = 7 on.
-/

namespace OMA.S_oeis_a171854

open PowerSeries

/-- The corrected recurrence (n ≥ 7): Mathar's recurrence, which fails at n = 6. -/
theorem main : ∀ T G : ℚ⟦X⟧, T = 1 + X * T + X ^ 2 * T * (T - 1) →
    G * (1 - X ^ 2 * T ^ 2) = X ^ 2 * (1 - X ^ 2) * T ^ 2 * (T - 1) →
    ∀ n : ℕ, 7 ≤ n →
      (17858 + 6149 * (n : ℚ) - 1390 * (n : ℚ) ^ 2) * coeff n G + (-20107 - 25542 * (n : ℚ) + 4884 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-2249 - 6110 * (n : ℚ) + 60 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-115735 + 49134 * (n : ℚ) - 5080 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-98877 + 66210 * (n : ℚ) - 8476 * (n : ℚ) ^ 2) * coeff (n - 4) G + (-109281 + 41338 * (n : ℚ) - 3652 * (n : ℚ) ^ 2) * coeff (n - 5) G +
        (69951 - 30139 * (n : ℚ) + 2878 * (n : ℚ) ^ 2) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a171854
