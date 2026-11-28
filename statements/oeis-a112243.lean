import Mathlib

/-!
# OEIS A112243

Paul Barry's exponential generating function is exp(x(1+x)/(1-2x)).
The order-three recurrence is due to R. J. Mathar (2015), and the formal
differential equation to Peter Bala (2022). Source: https://oeis.org/A112243.
-/

namespace OMA.S_oeis_a112243

open PowerSeries

noncomputable def exponent : PowerSeries ℚ :=
  X * (1 + X) * (1 - 2 * X)⁻¹

noncomputable def series : PowerSeries ℚ := (PowerSeries.exp ℚ).subst exponent

/-- EGF normalization: a(n) is n! times the coefficient of degree n. -/
noncomputable def a (n : ℕ) : ℚ := n.factorial * coeff n series

theorem main :
    constantCoeff series = 1 ∧
    (4 * X^2 - 4 * X + 1) * derivative ℚ series +
      (2 * X^2 - 2 * X - 1) * series = 0 ∧
    ∀ k : ℕ, let n : ℚ := k + 3
      a (k+3) + (-4*n+3)*a (k+2) + 2*(n-1)*(2*n-5)*a (k+1) +
        2*(n-1)*(n-2)*a k = 0 := by
  sorry

end OMA.S_oeis_a112243
