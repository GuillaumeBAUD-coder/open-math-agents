import Mathlib

namespace OMA.S_oeis_a129507

open PowerSeries

/-- Conjecture on OEIS A129507:
If `G : ℕ → ℚ⟦X⟧` satisfies the continued fraction `G(k) = 1 + X / (1 + X^2 / G(k + 1))`
(expressed without division as `(G(k + 1) + X^2) * (G(k) - 1) = X * G(k + 1)` with `G(k)(0) = 1`),
and `invG0` is the inverse of `G(0)` (`G(0) * invG0 = 1`), then
`A(X) := 4 * X^2 * (1 - invG0)` satisfies the algebraic equation of OEIS A129507:
`(1 + X + X^2 - A(X) / 2)^2 = 1 + 2*X + 3*X^2 - 2*X^3 + X^4`
(with `A(0) = 0`, matching `A(X) = 2 * (1 + X + X^2 - sqrt(1 + 2*X + 3*X^2 - 2*X^3 + X^4))`). -/
theorem main :
    ∀ (G : ℕ → PowerSeries ℚ) (invG0 : PowerSeries ℚ),
      (∀ k, PowerSeries.coeff 0 (G k) = 1) →
      (∀ k, (G (k + 1) + PowerSeries.X ^ 2) * (G k - 1) = PowerSeries.X * G (k + 1)) →
      G 0 * invG0 = 1 →
      let A : PowerSeries ℚ := PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 2 * (1 - invG0)
      (1 + PowerSeries.X + PowerSeries.X ^ 2 - PowerSeries.C (1 / 2 : ℚ) * A) ^ 2 =
        1 + PowerSeries.C (2 : ℚ) * PowerSeries.X + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 2 -
        PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 := by
  sorry

end OMA.S_oeis_a129507
