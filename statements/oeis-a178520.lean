import Mathlib

/-!
# A178520: Mathar's recurrence

Source: https://oeis.org/A178520
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A178520 (offset 0): number of ordered trees with n edges and with no vertex of outdegree 2 that have two leaves as their two children;
data 1, 1, 1, 4, 11, 32, 98, 309, 998, 3285, 10981, 37178, ...

Conjecture (R. J. Mathar, Jan 28 2020): D-finite with recurrence
(n+1)*a(n) +(n+2)*a(n-1) +(n+9)*a(n-2) +(-82*n+203)*a(n-3) +5*(2*n-9)*a(n-4) +21*(2*n-11)*a(n-5)
+(n-8)*a(n-6) +5*(n-9)*a(n-7) +21*(n-10)*a(n-8) = 0.

Formalization: G is the formal power series over ℚ with (G + x^2)*(1 - x*G) = 1, the equation for the g.f. given in the
entry (it has exactly one power series solution, with constant term 1);
a(n) = [x^n] G. The recurrence involves a(n-8), so it is stated for n ≥ 8; it is checked by the data, for
example at n = 8: (9)*(998) + (10)*(309) + (17)*(98) + (-453)*(32) + (35)*(11) + (105)*(4) + (0)*(1) + (-5)*(1) + (-42)*(1) = 0.
-/

namespace OMA.S_oeis_a178520

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A178520, for n ≥ 8. -/
theorem main : ∀ G : ℚ⟦X⟧, (G + X ^ 2) * (1 - X * G) = 1 →
    ∀ n : ℕ, 8 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (2 + (n : ℚ)) * coeff (n - 1) G +
        (9 + (n : ℚ)) * coeff (n - 2) G + (203 - 82 * (n : ℚ)) * coeff (n - 3) G +
        (-45 + 10 * (n : ℚ)) * coeff (n - 4) G + (-231 + 42 * (n : ℚ)) * coeff (n - 5) G +
        (-8 + (n : ℚ)) * coeff (n - 6) G + (-45 + 5 * (n : ℚ)) * coeff (n - 7) G +
        (-210 + 21 * (n : ℚ)) * coeff (n - 8) G = 0 := by
  sorry

end OMA.S_oeis_a178520
