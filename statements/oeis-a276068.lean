import Mathlib

/-!
# A276068: Mathar's recurrence

Source: https://oeis.org/A276068
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A276068 (offset 2): sum of the lengths of the first descents in all bargraphs having semiperimeter n (n>=2). A descent is a maximal sequence of consecutive down steps;
data 1, 3, 9, 26, 74, 210, 598, 1715, 4963, 14504, 42808, 127553, ...

Conjecture (R. J. Mathar, Jul 22 2022): D-finite with recurrence
(n+1)*a(n) +(-6*n+1)*a(n-1) +(10*n-13)*a(n-2) +(-4*n+13)*a(n-3) +(n-4)*a(n-4) +2*(-n+6)*a(n-5) = 0.

Formalization: The entry gives the g.f. in closed form, (1-z)*(1-2z-z^2-Q)/(2z*(1-2z)) with
Q = sqrt((1-z)*(1-3z-z^2-z^3)). S (the Q of the entry) is the formal power series over ℚ with
S^2 = (1-x)*(1-3*x-x^2-x^3), written out in `main`, and constant term 1 (the constant term selects the
branch of the square root), and G is determined by 2*x*(1-2*x)*G = (1-x)*(1-2*x-x^2-S);
a(n) = [x^n] G. The sequence has offset 2, and [x^k] G = 0 for k < 2. The recurrence involves a(n-5); with
a(k) read as [x^k] G (so a(k) = 0 below the offset) it holds for n ≥ 6, and `main` is stated
for this range, which contains every n ≥ 7 (where all indices are at least the offset).
It is checked by the data, for example at n = 6:
(7)*(74) + (-35)*(26) + (47)*(9) + (-11)*(3) + (2)*(1) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a276068

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A276068, for n ≥ 6. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X + 2 * X ^ 2 + X ^ 4 →
    coeff 0 S = 1 →
    2 * X * (1 - 2 * X) * G = (1 - X) * (1 - 2 * X - X ^ 2 - S) →
    ∀ n : ℕ, 6 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (1 - 6 * (n : ℚ)) * coeff (n - 1) G +
        (-13 + 10 * (n : ℚ)) * coeff (n - 2) G + (13 - 4 * (n : ℚ)) * coeff (n - 3) G +
        (-4 + (n : ℚ)) * coeff (n - 4) G + (12 - 2 * (n : ℚ)) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a276068
