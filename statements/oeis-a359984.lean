import Mathlib

/-!
# A359984: Mathar's recurrence

Source: https://oeis.org/A359984
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A359984 (offset 0): number of non-crossing antichain covers of {1,...,n} without singletons;
data 1, 0, 1, 5, 40, 372, 3815, 41652, 474980, 5591912, 67454545, 829438722, ...

Conjecture (R. J. Mathar, Mar 10 2023): D-finite with recurrence
8*n*(n-1)*a(n) -4*(n-1)*(56*n-145)*a(n-1) +4*(101*n^2-682*n+996)*a(n-2)
+2*(6200*n^2-47903*n+88131)*a(n-3) +2*(26985*n^2-234056*n+491978)*a(n-4)
+2*(62749*n^2-628865*n+1584314)*a(n-5) +(n-5)*(121577*n-667756)*a(n-6) +38285*(n-5)*(n-6)*a(n-7) =
0.

Formalization: T is the series F of the entry: the formal power series over ℚ with
T = 1 + (4*x + x^2)*T^2 - 3*x^2*(1+x)*T^3 (this equation has exactly one power series solution, with
constant term 1); and the g.f. G is given by G = 1 + x^2*T^2 - 3*x^3*T^3;
a(n) = [x^n] G. The recurrence involves a(n-7), so it is stated for n ≥ 7; it is checked by the data, for
example at n = 7: (336)*(41652) + (-5928)*(3815) + (4684)*(372) + (113220)*(40) + (351702)*(5) + (513920)*(1) + (366566)*(0) + (76570)*(1) = 0.
-/

namespace OMA.S_oeis_a359984

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A359984, for n ≥ 7. -/
theorem main : ∀ T G : ℚ⟦X⟧, T = 1 + (4 * X + X ^ 2) * T ^ 2 - 3 * X ^ 2 * (1 + X) * T ^ 3 →
    G = 1 + X ^ 2 * T ^ 2 - 3 * X ^ 3 * T ^ 3 →
    ∀ n : ℕ, 7 ≤ n →
      (-8 * (n : ℚ) + 8 * (n : ℚ) ^ 2) * coeff n G + (-580 + 804 * (n : ℚ) - 224 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (3984 - 2728 * (n : ℚ) + 404 * (n : ℚ) ^ 2) * coeff (n - 2) G + (176262 - 95806 * (n : ℚ) + 12400 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (983956 - 468112 * (n : ℚ) + 53970 * (n : ℚ) ^ 2) * coeff (n - 4) G + (3168628 - 1257730 * (n : ℚ) + 125498 * (n : ℚ) ^ 2) * coeff (n - 5) G +
        (3338780 - 1275641 * (n : ℚ) + 121577 * (n : ℚ) ^ 2) * coeff (n - 6) G + (1148550 - 421135 * (n : ℚ) + 38285 * (n : ℚ) ^ 2) * coeff (n - 7) G = 0 := by
  sorry

end OMA.S_oeis_a359984
