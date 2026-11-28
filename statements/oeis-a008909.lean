import Mathlib

namespace OMA.S_oeis_a008909

/-- The 5-step constant-`k` continued fraction for OEIS A008909:
`G(k) = 1 - 1 / (1 - x / (1 - x / (1 - x / (1 - x / (x - 1/G(k+1))))))`,
where `G(k) = G` is constant in `k` with `G(0) = 0`.
Eliminating `1/G` cleanly via `H = X * G - 1` (which has constant term `-1`, hence is a unit):
`D4 * (X * G - 1) = -1`, `D3 * D4 = D4 - X`, `D2 * D3 = D3 - X`, `D1 * D2 = D2 - X`,
`(1 - G) * D1 = 1` (with `D1(0) = D2(0) = D3(0) = D4(0) = 1`). -/
def IsCF008909 (G : PowerSeries ℚ) : Prop :=
  PowerSeries.coeff 0 G = 0 ∧
  ∃ D1 D2 D3 D4 : PowerSeries ℚ,
    PowerSeries.coeff 0 D4 = 1 ∧
    PowerSeries.coeff 0 D3 = 1 ∧
    PowerSeries.coeff 0 D2 = 1 ∧
    PowerSeries.coeff 0 D1 = 1 ∧
    D4 * (PowerSeries.X * G - 1) = -1 ∧
    D3 * D4 = D4 - PowerSeries.X ∧
    D2 * D3 = D3 - PowerSeries.X ∧
    D1 * D2 = D2 - PowerSeries.X ∧
    (1 - G) * D1 = 1

/-- OEIS A008909 conjecture equivalence:
The conjectured continued fraction generating function `A(x) = x * (1 - G/(1 - x))`
(offset 1) equals the conjectured algebraic generating function
`(2*x^3 - x^2 + 2*x - 1 + sqrt(x^4 + 2*x^2 - 4*x + 1)) / (2*x^2 - 2*x)`.
Formally, for any `G` satisfying `IsCF008909 G` and `A` with
`(1 - X) * A = X * (1 - X - G)`, `A` satisfies the algebraic equation
`((2*X^2 - 2*X) * A - (2*X^3 - X^2 + 2*X - 1))^2 = X^4 + 2*X^2 - 4*X + 1`. -/
theorem main :
    ∀ (G A : PowerSeries ℚ),
      IsCF008909 G →
      (1 - PowerSeries.X) * A = PowerSeries.X * (1 - PowerSeries.X - G) →
      ((PowerSeries.C 2 * PowerSeries.X ^ 2 - PowerSeries.C 2 * PowerSeries.X) * A -
        (PowerSeries.C 2 * PowerSeries.X ^ 3 - PowerSeries.X ^ 2 +
          PowerSeries.C 2 * PowerSeries.X - 1)) ^ 2 =
        PowerSeries.X ^ 4 + PowerSeries.C 2 * PowerSeries.X ^ 2 -
          PowerSeries.C 4 * PowerSeries.X + 1 := by
  sorry

end OMA.S_oeis_a008909
