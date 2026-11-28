import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

namespace OMA.S_oeis_a303562

/-- OEIS A303562: If `A(x) ∈ ℤ[[x]]` has `a(0) = 1`, `a(1) = 1`, and satisfies
`[x^(n-1)] (1 / A(x))^(n^2 + n - 1) = 0` for all `n > 2`, then `a(n)` is odd if and only if
`n = (4^k - 1) / 3` for some `k ≥ 0`. -/
theorem main :
    ∀ (A : PowerSeries ℤ),
      PowerSeries.constantCoeff A = 1 →
      PowerSeries.coeff 1 A = 1 →
      (∀ n : ℕ, 2 < n → PowerSeries.coeff (n - 1) ((Ring.inverse A) ^ (n ^ 2 + n - 1)) = 0) →
      ∀ n : ℕ, Odd (PowerSeries.coeff n A) ↔ ∃ k : ℕ, n = (4 ^ k - 1) / 3 := by
  sorry

end OMA.S_oeis_a303562
