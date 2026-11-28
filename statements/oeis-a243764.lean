import Mathlib

/-!
# A243764: Mathar's recurrence, corrected to n ≥ 7

Source: https://oeis.org/A243764
Credit: @ivillar

Status: false as stated at n = 6 (the left side is 24576 at n = 6 on the OEIS data); `main` is the
corrected recurrence (n ≥ 7), which is proved.

A243764 (offset 0): expansion of -((2*sqrt(1-4*x)-2)*x)/(sqrt(8*x+4*sqrt(1-4*x)-3)-1);
data -1, 1, 3, 4, 13, 36, 122, 408, 1453, 5236, 19374, 72616, ...

Conjecture (R. J. Mathar, Jun 07 2016):
245*n*(n-1)*(n-2)*a(n) -140*(n-1)*(n-2)*(28*n-81)*a(n-1) +4*(n-2)*(5812*n^2-41488*n+72261)*a(n-2)
+16*(-3368*n^3+45144*n^2-191968*n+260859)*a(n-3) +128*(-152*n^3-768*n^2+16748*n-45483)*a(n-4)
+2048*(2*n-11)*(74*n^2-715*n+1629)*a(n-5) -98304*(n-7)*(2*n-11)*(2*n-13)*a(n-6) = 0.

Formalization: T is the formal power series over ℚ with T^2 = 1-4*x and constant term 1; W is the formal power
series with W^2 = 8*x + 4*T - 3 and constant term 1, that is W = sqrt(8x + 4*sqrt(1-4x) - 3) (the
constant terms select the branches of the square roots); and G is determined by
G*(W - 1) = -(2*T - 2)*x (its constant term follows from the other conditions and is recorded as a
hypothesis);
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 7): on the data the left side of the recurrence as
stated is 24576 at n = 6, and it vanishes from n = 7 on.
-/

namespace OMA.S_oeis_a243764

open PowerSeries

/-- The corrected recurrence (n ≥ 7): Mathar's recurrence, which fails at n = 6. -/
theorem main : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    coeff 0 T = 1 →
    W ^ 2 = 8 * X + 4 * T - 3 →
    coeff 0 W = 1 →
    G * (W - 1) = -((2 * T - 2) * X) →
    coeff 0 G = -1 →
    ∀ n : ℕ, 7 ≤ n →
      (490 * (n : ℚ) - 735 * (n : ℚ) ^ 2 + 245 * (n : ℚ) ^ 3) * coeff n G + (22680 - 41860 * (n : ℚ) + 23100 * (n : ℚ) ^ 2 - 3920 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-578088 + 620948 * (n : ℚ) - 212448 * (n : ℚ) ^ 2 + 23248 * (n : ℚ) ^ 3) * coeff (n - 2) G + (4173744 - 3071488 * (n : ℚ) + 722304 * (n : ℚ) ^ 2 - 53888 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (-5821824 + 2143744 * (n : ℚ) - 98304 * (n : ℚ) ^ 2 - 19456 * (n : ℚ) ^ 3) * coeff (n - 4) G + (-36698112 + 22779904 * (n : ℚ) - 4595712 * (n : ℚ) ^ 2 + 303104 * (n : ℚ) ^ 3) * coeff (n - 5) G +
        (98402304 - 47087616 * (n : ℚ) + 7471104 * (n : ℚ) ^ 2 - 393216 * (n : ℚ) ^ 3) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a243764
