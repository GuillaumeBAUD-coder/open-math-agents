import Mathlib

namespace OMA.S_oeis_a079555

/-- OEIS A079555: Decimal expansion of `∏_{k ≥ 1} (1 + 1 / 2^k)`.
Conjecture (Schulte):
`∏_{k ≥ 1} (1 + 1 / 2^k) = 2 + ∑_{k ≥ 2} 1 / ∏_{i = 2}^k (2^i - 1)`. -/
theorem main :
    Filter.Tendsto
      (fun N : ℕ => ∏ k ∈ Finset.Icc 1 N, (1 + (1 / 2 : ℝ) ^ k))
      Filter.atTop
      (nhds (2 + ∑' k : ℕ, (1 : ℝ) / ∏ i ∈ Finset.Icc 2 (k + 2), ((2 : ℝ) ^ i - 1))) := by
  sorry

end OMA.S_oeis_a079555
