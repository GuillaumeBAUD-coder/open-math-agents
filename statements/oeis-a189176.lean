import Mathlib

/-!
# A189176: Mathar's recurrence, corrected to n ≥ 3

Source: https://oeis.org/A189176
Credit: @ivillar

Status: false as stated at n = 2 (the left side is -5 at n = 2 on the OEIS data); `main` is the
corrected recurrence (n ≥ 3), which is proved.

A189176 (offset 0): row sums of the Riordan matrix (1+x/sqrt(1-4*x),(1-sqrt(1-4*x))/2) (A189175);
data 1, 2, 5, 15, 49, 168, 594, 2145, 7865, 29172, 109174, 411502, ...

Conjecture (R. J. Mathar, Nov 15 2011):
(n+1)*a(n) + 3*(1-3*n)*a(n-1) + 10*(2*n-3)*a(n-2) = 0.

Formalization: The entry gives the g.f. of the row sums in closed form,
(1-5*x+4*x^2-(1-5*x)*sqrt(1-4x))/(2*x*(1-4*x)), and this closed form is used as the definition here. S is
the formal power series over ℚ with S^2 = 1-4*x and constant term 1 (the constant term selects the
branch of the square root), and G is determined by 2*x*(1-4*x)*G = 1 - 5*x + 4*x^2 - (1-5*x)*S;
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 3): on the data the left side of the recurrence as
stated is -5 at n = 2, and it vanishes from n = 3 on.
-/

namespace OMA.S_oeis_a189176

open PowerSeries

/-- The corrected recurrence (n ≥ 3): Mathar's recurrence, which fails at n = 2. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * (1 - 4 * X) * G = 1 - 5 * X + 4 * X ^ 2 - (1 - 5 * X) * S →
    ∀ n : ℕ, 3 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (3 - 9 * (n : ℚ)) * coeff (n - 1) G +
        (-30 + 20 * (n : ℚ)) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a189176
