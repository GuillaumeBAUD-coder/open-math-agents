import Mathlib

/-!
# A273905: Mathar's recurrence

Source: https://oeis.org/A273905
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A273905 (offset 2): number of symmetric bargraphs having semiperimeter n (n>=2);
data 1, 2, 3, 5, 9, 15, 27, 46, 83, 143, 259, 450, ...

Conjecture (R. J. Mathar, Jul 22 2022): D-finite with recurrence
(n+1)*a(n) +2*(-1)*a(n-1) +2*(-2*n+3)*a(n-2) +2*(n-6)*a(n-4) +6*(1)*a(n-5) -2*a(n-6) +(n-9)*a(n-8)
= 0.

Formalization: The entry gives the g.f. in closed form, (1+z)*(z^4+2z^3+2z^2-1+Q)/(2z*(1-z-z^2-z^3)) with
Q = sqrt((1-z^2)*(1-z-z^2-z^3)*(1+z-z^2+z^3)). S (the Q of the entry) is the formal power series over ℚ with
S^2 = (1-x^2)*(1-x-x^2-x^3)*(1+x-x^2+x^3), written out in `main`, and constant term 1 (the constant term
selects the branch of the square root), and G is determined by
2*x*(1-x-x^2-x^3)*G = (1+x)*(x^4+2*x^3+2*x^2-1+S);
a(n) = [x^n] G. The sequence has offset 2, and [x^k] G = 0 for k < 2. The recurrence involves a(n-8); with
a(k) read as [x^k] G (so a(k) = 0 below the offset) it holds for n ≥ 9, and `main` is stated
for this range, which contains every n ≥ 10 (where all indices are at least the offset).
It is checked by the data, for example at n = 9:
(10)*(46) + (-2)*(27) + (-30)*(15) + (6)*(5) + (6)*(3) + (-2)*(2) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a273905

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A273905, for n ≥ 9. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X ^ 2 + 2 * X ^ 4 + X ^ 8 →
    coeff 0 S = 1 →
    2 * X * (1 - X - X ^ 2 - X ^ 3) * G = (1 + X) * (X ^ 4 + 2 * X ^ 3 + 2 * X ^ 2 - 1 + S) →
    ∀ n : ℕ, 9 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (-2) * coeff (n - 1) G +
        (6 - 4 * (n : ℚ)) * coeff (n - 2) G + (-12 + 2 * (n : ℚ)) * coeff (n - 4) G +
        (6) * coeff (n - 5) G + (-2) * coeff (n - 6) G +
        (-9 + (n : ℚ)) * coeff (n - 8) G = 0 := by
  sorry

end OMA.S_oeis_a273905
