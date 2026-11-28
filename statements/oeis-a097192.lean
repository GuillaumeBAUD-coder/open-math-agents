import Mathlib

/-!
# A097192: Mathar's recurrence

Source: https://oeis.org/A097192
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A097192 (offset 0): main diagonal of triangle A097190, in which the n-th row polynomial R_n(y) is formed from the initial (n+1) terms of g.f. A097191(y)^(n+1), where R_n(1/3) = 9^n for all n>=0;
data 1, 24, 612, 15912, 417690, 11027016, 292215924, 7764594552, 206732329947, 5512862131920, 147193418922264, 3934078651195056, ...

Conjecture (R. J. Mathar, Nov 16 2012):
n*a(n) +3*(1-9*n)*a(n-1) = 0.

Formalization: The entry gives the g.f. A(x) = 1/(1-27*x)^(8/9). G is the formal power series over ℚ with constant term 1
and G^9*(1-27*x)^8 = 1, that is the ninth root of 1/(1-27x)^8 with constant term 1 (over ℚ the constant
term of such a root is necessarily 1; it is recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-1), so it is stated for n ≥ 1; it is checked by the data, for
example at n = 1: (1)*(24) + (-24)*(1) = 0.
-/

namespace OMA.S_oeis_a097192

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A097192, for n ≥ 1. -/
theorem main : ∀ G : ℚ⟦X⟧, coeff 0 G = 1 →
    G ^ 9 * (1 - 27 * X) ^ 8 = 1 →
    ∀ n : ℕ, 1 ≤ n →
      ((n : ℚ)) * coeff n G + (3 - 27 * (n : ℚ)) * coeff (n - 1) G = 0 := by
  sorry

end OMA.S_oeis_a097192
