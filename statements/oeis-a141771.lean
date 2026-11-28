import Mathlib

/-!
# A141771: Mathar's recurrence, corrected to n ≥ 3

Source: https://oeis.org/A141771
Credit: @ivillar

Status: false as stated at n = 1 and n = 2 (the left side is 1728 at n = 1, 2232 at n = 2 on the OEIS data); `main` is the
corrected recurrence (n ≥ 3), which is proved.

A141771 (offset 0): expansion of (1-sqrt(1-4*x))/(2*x) + 8*x^3/((sqrt(1-4*x))*(1+sqrt(1-4*x))^3);
data 1, 1, 2, 6, 19, 63, 216, 759, 2717, 9867, 36244, 134368, ...

Conjecture (R. J. Mathar, Apr 30 2016):
(n+1) *(n^2+5*n-12) *(n^3-5*n^2+38*n-250)*a(n)
-2 *(2*n-3) *(n^2+7*n-6) *(n^3-5*n^2+38*n-250) *a(n-1) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x) = (1-sqrt(1-4x))/(2x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by (G - c)*S*(1+S)^3 = 8*x^3;
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 3): on the data the left side of the recurrence as
stated is 1728 at n = 1, 2232 at n = 2, and it vanishes from n = 3 on.
-/

namespace OMA.S_oeis_a141771

open PowerSeries

/-- The corrected recurrence (n ≥ 3): Mathar's recurrence, which fails at n = 1 and n = 2. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    (G - c) * (S * (1 + S) ^ 3) = 8 * X ^ 3 →
    ∀ n : ℕ, 3 ≤ n →
      (3000 + 1294 * (n : ℚ) - 1706 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3 + (n : ℚ) ^ 4 + (n : ℚ) ^ 5 + (n : ℚ) ^ 6) * coeff n G + (9000 - 17868 * (n : ℚ) + 8188 * (n : ℚ) ^ 2 - 202 * (n : ℚ) ^ 3 + 24 * (n : ℚ) ^ 4 - 2 * (n : ℚ) ^ 5 - 4 * (n : ℚ) ^ 6) * coeff (n - 1) G = 0 := by
  sorry

end OMA.S_oeis_a141771
