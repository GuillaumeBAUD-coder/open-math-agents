import Mathlib

namespace OMA.S_oeis_a007549

/-- The formal exponential power series `exp(x) = ∑_{k ≥ 0} x^k / k!` over `ℚ`. -/
noncomputable def expSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun k => (1 : ℚ) / (k.factorial : ℚ))

/-- The differential operator `D = exp(x) * (1 + x) * d/dx` on `PowerSeries ℚ`. -/
noncomputable def balaD (F : PowerSeries ℚ) : PowerSeries ℚ :=
  expSeries * (1 + PowerSeries.X) * PowerSeries.derivative ℚ F

/-- OEIS A007549 ("shifts left when exponentiated twice"):
Its exponential generating function `A(x) = ∑_{n ≥ 1} a(n) x^n / n!` satisfies `A(0) = 0` and
`A'(x) = exp(exp(A(x)) - 1)`, i.e., there exist `E1, E2 ∈ ℚ[[x]]` with `E1(0) = 1`,
`E1' = A' * E1`, `E2(0) = 1`, `E2' = E1' * E2`, and `A' = E2`.
Conjecture (Peter Bala, Feb 24 2025): For all `n ≥ 1`,
`a(n) = (D^(n - 1) (exp(x)))|_{x = 0}` where `D = exp(x) * (1 + x) * d/dx`. -/
theorem main :
    ∀ A E1 E2 : PowerSeries ℚ,
      PowerSeries.constantCoeff A = 0 →
      PowerSeries.constantCoeff E1 = 1 →
      PowerSeries.derivative ℚ E1 = PowerSeries.derivative ℚ A * E1 →
      PowerSeries.constantCoeff E2 = 1 →
      PowerSeries.derivative ℚ E2 = PowerSeries.derivative ℚ E1 * E2 →
      PowerSeries.derivative ℚ A = E2 →
      ∀ n : ℕ, 1 ≤ n →
        (n.factorial : ℚ) * PowerSeries.coeff n A =
        PowerSeries.constantCoeff (balaD^[n - 1] expSeries) := by
  sorry

end OMA.S_oeis_a007549
