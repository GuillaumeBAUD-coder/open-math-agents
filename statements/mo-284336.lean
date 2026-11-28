import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Intervals

namespace OMA.S_mo_284336

noncomputable def harmonic (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range r, 1 / ((j + 1 : ℕ) : ℝ)

noncomputable def normalizer (r : ℕ) (q : ℝ) : ℝ :=
  ∑ j ∈ Finset.range r, ((j + 1 : ℕ) : ℝ) ^ q

/-- Each inner sum takes the largest `m+1` indices in descending order. -/
noncomputable def series (r : ℕ) (p q : ℝ) : ℝ :=
  ∑ m ∈ Finset.range r,
    (∑ j ∈ Finset.range (m + 1),
      ((((r - j : ℕ) : ℝ) ^ q) / normalizer r q) ^ (1 / p))⁻¹

/-- Two-sided bounds for the sum in the question, with conjugate exponents. -/
theorem main :
    ∀ (r : ℕ) (p q : ℝ), 0 < r → 1 < p → 1 < q → 1 / p + 1 / q = 1 →
      (q + 1) ^ (-(1 / p)) * (r : ℝ) ^ (1 / p) * harmonic r ≤ series r p q ∧
        series r p q ≤ q * (r : ℝ) ^ (1 / p) * harmonic r := by
  sorry

end OMA.S_mo_284336
