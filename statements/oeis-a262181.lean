import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Fintype.Fin

namespace OMA.S_oeis_a262181

/-- Cumulative exterior turning count (in units of `π / n`) before edge `k`. -/
def cumTurn (n : ℕ) (m : Fin n → ℕ) (k : Fin n) : ℕ :=
  ∑ j : Fin n, if j.1 < k.1 then n - m j else 0

/-- A sequence `m : Fin n → ℕ` represents a closed convex equilateral `n`-gon with interior corner
angles `m(k) * π / n` (`0 < m(k) ≤ n`) when `1 ≤ m k ≤ n` for all `k`, the exterior turning angles
`(n - m k) * π / n` sum to `2π` (`∑ k, (n - m k) = 2 * n`), and the `n` unit edge vectors sum to
`0` in `ℂ`. -/
def IsConvexEquilateralAngles (n : ℕ) (m : Fin n → ℕ) : Prop :=
  (∀ k : Fin n, 1 ≤ m k ∧ m k ≤ n) ∧
  (∑ k : Fin n, (n - m k)) = 2 * n ∧
  (∑ k : Fin n, Complex.exp (Complex.I * (cumTurn n m k : ℝ) * Real.pi / (n : ℝ))) = 0

/-- Conjecture (OEIS A262181): for every odd prime `p` (`p ≥ 3`), there is only one convex
equilateral `p`-gon with corner angles of the form `m * π / p` (`0 < m ≤ p`), namely the
regular `p`-gon (`m(k) = p - 2` for all `k`). -/
theorem main : ∀ p : ℕ, p.Prime → 3 ≤ p →
    ∃! m : Fin p → ℕ, IsConvexEquilateralAngles p m := by
  sorry

end OMA.S_oeis_a262181
