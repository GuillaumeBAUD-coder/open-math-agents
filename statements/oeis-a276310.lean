import Mathlib

/-!
# A276310: Mathar's recurrence

Source: https://oeis.org/A276310
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A276310 (offset 1): g.f. A(x) satisfies: x = A(x)-2*A(x)^2-2*A(x)^3;
data 1, 2, 10, 60, 404, 2912, 21984, 171600, 1373680, 11215776, 93039648, 781936896, ...

Conjecture (R. J. Mathar, Sep 17 2016):
3*n*(n-1)*a(n) -13*(n-1)*(2*n-3)*a(n-1) -3*(3*n-5)*(3*n-7)*a(n-2) = 0.

Formalization: G is the formal power series over ℚ with zero constant term and x = G - 2*G^2 - 2*G^3 (the
series reversion of x - 2*x^2 - 2*x^3);
a(n) = [x^n] G. The sequence has offset 1 and the recurrence involves a(n-2), so it is stated for n ≥ 3,
where every index is at least the offset; it is checked by the data, for example at n = 3:
(18)*(10) + (-78)*(2) + (-24)*(1) = 0.
-/

namespace OMA.S_oeis_a276310

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A276310, for n ≥ 3. -/
theorem main : ∀ G : ℚ⟦X⟧, coeff 0 G = 0 →
    X = G - 2 * G ^ 2 - 2 * G ^ 3 →
    ∀ n : ℕ, 3 ≤ n →
      (-3 * (n : ℚ) + 3 * (n : ℚ) ^ 2) * coeff n G + (-39 + 65 * (n : ℚ) - 26 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-105 + 108 * (n : ℚ) - 27 * (n : ℚ) ^ 2) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a276310
