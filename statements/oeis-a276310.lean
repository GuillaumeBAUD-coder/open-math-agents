import Mathlib

/-!
# A276310: Mathar's recurrence, corrected to n ≥ 3

Source: https://oeis.org/A276310
Credit: @ivillar

Status: false as stated at n = 2 (the left side is -1 at n = 2 on the OEIS data); `main` is the
corrected recurrence (n ≥ 3), which is proved.

A276310 (offset 1): g.f. A(x) satisfies: x = A(x)-2*A(x)^2-2*A(x)^3;
data 1, 2, 10, 60, 404, 2912, 21984, 171600, 1373680, 11215776, 93039648, 781936896, ...

Conjecture (R. J. Mathar, Sep 17 2016):
3*n*(n-1)*a(n) -13*(n-1)*(2*n-3)*a(n-1) -3*(3*n-5)*(3*n-7)*a(n-2) = 0.

Formalization: G is the formal power series over ℚ with zero constant term and x = G - 2*G^2 - 2*G^3 (the
series reversion of x - 2*x^2 - 2*x^3);
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 3): on the data the left side of the recurrence as
stated is -1 at n = 2, and it vanishes from n = 3 on.
-/

namespace OMA.S_oeis_a276310

open PowerSeries

/-- The corrected recurrence (n ≥ 3): Mathar's recurrence, which fails at n = 2. -/
theorem main : ∀ G : ℚ⟦X⟧, coeff 0 G = 0 →
    X = G - 2 * G ^ 2 - 2 * G ^ 3 →
    ∀ n : ℕ, 3 ≤ n →
      (-3 * (n : ℚ) + 3 * (n : ℚ) ^ 2) * coeff n G + (-39 + 65 * (n : ℚ) - 26 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-105 + 108 * (n : ℚ) - 27 * (n : ℚ) ^ 2) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a276310
