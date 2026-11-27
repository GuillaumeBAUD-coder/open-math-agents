import Mathlib

/-!
# A174015: A generalized Catalan number sequence.

Source: https://oeis.org/A174015
Credit: @sntntHb

The sequence has g.f. `(sqrt(1-2x+x^2+4x^3)+3x-1)/(2x(1-x))` (offset 0).
R. J. Mathar (Nov 13 2012) conjectured the recurrence
`(n+1)*a(n) -3*n*a(n-1) +3*(n-1)*a(n-2) +3*(n-4)*a(n-3) +2*(7-2*n)*a(n-4) = 0`.

Formalization: `S` is the power series square root of `1-2x+x^2+4x^3` with constant
term `1`, and `G` is the g.f., characterized by `2x(1-x) G = S + 3x - 1` (this determines
`G` uniquely). The recurrence is stated for all `n ≥ 4`, where every index is defined.
Checked numerically (exact rationals) for 4 ≤ n < 40; the first terms of `G` are
1, 1, 2, 3, 4, 4, 2, -3, -10, -14, -4, 34, ... as in the OEIS entry.
-/

namespace OMA.S_oeis_a174015

open PowerSeries

theorem main : ∀ S G : PowerSeries ℚ,
    S ^ 2 = 1 - 2 * X + X ^ 2 + 4 * X ^ 3 → constantCoeff S = 1 →
    2 * X * (1 - X) * G = S + 3 * X - 1 →
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℚ) + 1) * coeff n G - 3 * (n : ℚ) * coeff (n - 1) G
        + 3 * ((n : ℚ) - 1) * coeff (n - 2) G + 3 * ((n : ℚ) - 4) * coeff (n - 3) G
        + 2 * (7 - 2 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a174015
