import Mathlib

/-!
# A134424: Mathar's recurrence

Source: https://oeis.org/A134424
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A134424 (offset 0): area under all paths in the first quadrant from (0,0) to (n,0) using steps U=(1,1), D=(1,-1), h=(1,0) and H=(2,0);
data 0, 0, 1, 4, 21, 80, 316, 1152, 4186, 14812, 52020, 180616, ...

Conjecture (R. J. Mathar, Jul 24 2022): D-finite with recurrence
-(n+2)*(5*n-7)*a(n) -(n+1)*(5*n-127)*a(n-1) +(135*n^2-655*n-42)*a(n-2) +2*(5*n^2-275*n-108)*a(n-3)
+(-725*n^2+4941*n-5734)*a(n-4) +(-235*n^2+1880*n-1173)*a(n-5) +(725*n^2-6659*n+12606)*a(n-6)
+2*(5*n^2+195*n-1988)*a(n-7) +(-135*n^2+1505*n-3358)*a(n-8) -(5*n+87)*(n-9)*a(n-9)
+(5*n-33)*(n-10)*a(n-10) = 0.

Formalization: T is the series g of the entry (the g.f. of A128720): the formal power series over ℚ with
T = 1 + x*T + x^2*T + x^2*T^2 (this equation has exactly one power series solution, with constant term
1); and the g.f. G is determined by
G*(1 + x - x^2)*(1 - 3*x - x^2) = x^2*(1 + x^2)*T^2;
a(n) = [x^n] G. The recurrence involves a(n-10), so it is stated for n ≥ 10; it is checked by the data, for
example at n = 10: (-516)*(52020) + (847)*(14812) + (6908)*(4186) + (-4716)*(1152) + (-28824)*(316) + (-5873)*(80) + (18516)*(21) + (924)*(4) + (-1808)*(1) + (-137)*(0) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a134424

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A134424, for n ≥ 10. -/
theorem main : ∀ T G : ℚ⟦X⟧, T = 1 + X * T + X ^ 2 * T + X ^ 2 * T ^ 2 →
    G * ((1 + X - X ^ 2) * (1 - 3 * X - X ^ 2)) = X ^ 2 * (1 + X ^ 2) * T ^ 2 →
    ∀ n : ℕ, 10 ≤ n →
      (14 - 3 * (n : ℚ) - 5 * (n : ℚ) ^ 2) * coeff n G + (127 + 122 * (n : ℚ) - 5 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-42 - 655 * (n : ℚ) + 135 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-216 - 550 * (n : ℚ) + 10 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-5734 + 4941 * (n : ℚ) - 725 * (n : ℚ) ^ 2) * coeff (n - 4) G + (-1173 + 1880 * (n : ℚ) - 235 * (n : ℚ) ^ 2) * coeff (n - 5) G +
        (12606 - 6659 * (n : ℚ) + 725 * (n : ℚ) ^ 2) * coeff (n - 6) G + (-3976 + 390 * (n : ℚ) + 10 * (n : ℚ) ^ 2) * coeff (n - 7) G +
        (-3358 + 1505 * (n : ℚ) - 135 * (n : ℚ) ^ 2) * coeff (n - 8) G + (783 - 42 * (n : ℚ) - 5 * (n : ℚ) ^ 2) * coeff (n - 9) G +
        (330 - 83 * (n : ℚ) + 5 * (n : ℚ) ^ 2) * coeff (n - 10) G = 0 := by
  sorry

end OMA.S_oeis_a134424
