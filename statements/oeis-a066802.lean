import Mathlib

/-!
# A066802: a(n) = binomial(6*n,3*n).

Source: https://oeis.org/A066802
Credit: @thatoneguy006

The conjecture stated here, from the entry (Peter Bala, Oct 27 2022):

  Conjecture: a(n) = [x^n] G(x)^(2*n), where
  G(x) = (1 + x)*(1 - 6*x + x^2)/(2*x) + (x^2 - 1)*sqrt(1 - 14*x + x^2)/(2*x)
       = 1 + 10*x + 81*x^2 + 720*x^3 + ....
  The algebraic function G(x) satisfies the quadratic equation
  x*G(x)^2 - (1 - 5*x - 5*x^2 + x^3)*G(x) + (1 + x)^4 = 0.

Reading. The square root is the power series `S` with `S^2 = 1 - 14X + X^2` and constant term
`1` (the branch for which the expansion 1 + 10x + 81x^2 + ... is a power series). Clearing the
denominator `2x`, `G` is the power series with `2X * G = (1 + X)(1 - 6X + X^2) + (X^2 - 1) S`;
the right side has zero constant term, and `X` is not a zero divisor, so `G` is determined.
With these, G = 1 + 10x + 81x^2 + 720x^3 + 7056x^4 + ..., as in the entry. The statement is
over ℚ and holds for all `n ≥ 0` (the offset of the entry is 0, and for n = 0 both sides are 1).
-/

namespace OMA.S_oeis_a066802

open PowerSeries

/-- Bala's conjecture: `C(6n, 3n) = [x^n] G(x)^(2n)`. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 14 * X + X ^ 2 → coeff 0 S = 1 →
    2 * X * G = (1 + X) * (1 - 6 * X + X ^ 2) + (X ^ 2 - 1) * S →
    ∀ n : ℕ, coeff n (G ^ (2 * n)) = ((6 * n).choose (3 * n) : ℚ) := by
  sorry

end OMA.S_oeis_a066802
