import Mathlib

/-!
# A285195: Mathar's recurrence

Source: https://oeis.org/A285195
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A285195 (offset 0): g.f.: 2C(x)/(3-sqrt(1-4xC(x))) where C = g.f. for A000108;
data 1, 0, 0, -1, -6, -30, -142, -660, -3054, -14154, -65886, -308442, ...

Conjecture (R. J. Mathar, Jan 25 2020): D-finite with recurrence
+126*n*(n-1)*(n+1)*a(n) -3*n*(n-1)*(691*n-1037)*a(n-1) +(n-1)*(12023*n^2-48049*n+47736)*a(n-2)
+2*(-12889*n^3+93970*n^2-221427*n+169506)*a(n-3) +4*(-248*n^3+12718*n^2-88433*n+160113)*a(n-4)
+16*(2918*n^3-41574*n^2+198532*n-317121)*a(n-5) +240*(4*n-19)*(2*n-9)*(4*n-21)*a(n-6) = 0.

Formalization: T is the formal power series over ℚ with T^2 = 1-4*x and constant term 1; U is the Catalan g.f.
C(x), determined by 2*x*U = 1 - T; V is the formal power series with V^2 = 1 - 4*x*U and constant term
1, that is V = sqrt(1 - 4*x*C(x)) (the constant terms select the branches of the square roots); and G
is determined by G*(3 - V) = 2*U (its constant term is recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-6), so it is stated for n ≥ 6; it is checked by the data, for
example at n = 6: (26460)*(-142) + (-279810)*(-30) + (961350)*(-6) + (-1120320)*(-1) + (135180)*(0) + (123120)*(0) + (10800)*(1) = 0.
-/

namespace OMA.S_oeis_a285195

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A285195, for n ≥ 6. -/
theorem main : ∀ T U V G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    coeff 0 T = 1 →
    2 * X * U = 1 - T →
    V ^ 2 = 1 - 4 * X * U →
    coeff 0 V = 1 →
    G * (3 - V) = 2 * U →
    coeff 0 G = 1 →
    ∀ n : ℕ, 6 ≤ n →
      (-126 * (n : ℚ) + 126 * (n : ℚ) ^ 3) * coeff n G + (-3111 * (n : ℚ) + 5184 * (n : ℚ) ^ 2 - 2073 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-47736 + 95785 * (n : ℚ) - 60072 * (n : ℚ) ^ 2 + 12023 * (n : ℚ) ^ 3) * coeff (n - 2) G + (339012 - 442854 * (n : ℚ) + 187940 * (n : ℚ) ^ 2 - 25778 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (640452 - 353732 * (n : ℚ) + 50872 * (n : ℚ) ^ 2 - 992 * (n : ℚ) ^ 3) * coeff (n - 4) G + (-5073936 + 3176512 * (n : ℚ) - 665184 * (n : ℚ) ^ 2 + 46688 * (n : ℚ) ^ 3) * coeff (n - 5) G +
        (-861840 + 537120 * (n : ℚ) - 111360 * (n : ℚ) ^ 2 + 7680 * (n : ℚ) ^ 3) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a285195
