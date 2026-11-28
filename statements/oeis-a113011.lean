import Mathlib

namespace OMA.S_oeis_a113011

/-- Partial numerator `a_n = 2n / (4n^2 - 1)` for `n ≥ 1` in Stefano Spezia's
conjectured continued fraction for `1 / (√e - 1)`. -/
noncomputable def cfNum (n : ℕ) : ℝ :=
  (2 * (n : ℝ)) / (4 * (n : ℝ) ^ 2 - 1)

/-- Finite continued fraction tail evaluator `K_{k=m}^{m+d-1} (cfNum k / 1)` with tail `x`. -/
noncomputable def cfFold : ℕ → ℕ → ℝ → ℝ
  | _, 0, x => x
  | m, d + 1, x => cfNum m / (1 + cfFold (m + 1) d x)

/-- `N`-th convergent of `1 + K_{n=1}^∞ (2n / (4n^2 - 1)) / 1`. -/
noncomputable def cfConv (N : ℕ) : ℝ :=
  1 + cfFold 1 N 0

/-- OEIS A113011 (Stefano Spezia, Dec 27 2024):
`1 / (√e - 1) = 1 + K_{n ≥ 1} (2n / (4n^2 - 1)) / 1`. -/
theorem main :
    Filter.Tendsto cfConv Filter.atTop (nhds (1 / (Real.sqrt (Real.exp 1) - 1))) := by sorry

end OMA.S_oeis_a113011
