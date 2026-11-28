import Mathlib

namespace OMA.S_oeis_a167199

open PowerSeries

/-- Conjecture on OEIS A167199:
The e.g.f. `2 / (2 + 4*X + X^2)` equals `G(0) / (1 + X)`, where `G : ℕ → ℚ⟦X⟧` satisfies
the recursively defined continued fraction
`G(k) = 1 - X / ((1 + X) - X*(1 + X) / (X - 2*(1 + X) / G(k + 1)))`
(expressed without division as
`((1 + X) * (X * G(k + 1) - 2 * (1 + X)) - X * (1 + X) * G(k + 1)) * (1 - G(k)) =
 X * (X * G(k + 1) - 2 * (1 + X))`, i.e.
`-2 * (1 + X)^2 * (1 - G(k)) = X * (X * G(k + 1) - 2 * (1 + X))` with `G(k)(0) = 1`).
Equivalently, `(2 + 4*X + X^2) * G(0) = 2 * (1 + X)`. -/
theorem main :
    ∀ G : ℕ → PowerSeries ℚ,
      (∀ k, PowerSeries.coeff 0 (G k) = 1) →
      (∀ k,
        ((1 + PowerSeries.X) * (PowerSeries.X * G (k + 1) - PowerSeries.C (2 : ℚ) * (1 + PowerSeries.X)) -
          PowerSeries.X * (1 + PowerSeries.X) * G (k + 1)) * (1 - G k) =
        PowerSeries.X * (PowerSeries.X * G (k + 1) - PowerSeries.C (2 : ℚ) * (1 + PowerSeries.X))) →
      (PowerSeries.C (2 : ℚ) + PowerSeries.C (4 : ℚ) * PowerSeries.X + PowerSeries.X ^ 2) * G 0 =
        PowerSeries.C (2 : ℚ) * (1 + PowerSeries.X) := by
  sorry

end OMA.S_oeis_a167199
