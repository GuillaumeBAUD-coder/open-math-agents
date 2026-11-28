import Mathlib

namespace OMA.S_mo_301135

open MeasureTheory

/-- Expected L1 distance between the sorted arrays `A_(i)` and `B_(i)` of length `n`
drawn i.i.d. from a probability distribution `μ` on `ℝ`. -/
noncomputable def expectedSortedDiff (n : ℕ) (μ : Measure ℝ) : ℝ :=
  ∫ ab : (Fin n → ℝ) × (Fin n → ℝ),
    (∑ i : Fin n, |ab.1 (Tuple.sort ab.1 i) - ab.2 (Tuple.sort ab.2 i)|)
    ∂((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ)))

/-- The symmetric Bernoulli(1/2) distribution supported on `{0, 1}`. -/
noncomputable def berHalf : Measure ℝ :=
  (1 / 2 : ENNReal) • Measure.dirac (0 : ℝ) + (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ)

/-- The uniform probability distribution on `[0, 1]`. -/
noncomputable def unif01 : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

theorem main :
    (∀ (n : ℕ) (μ : Measure ℝ), 1 ≤ n → IsProbabilityMeasure μ → μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
      expectedSortedDiff n μ ≤ (n : ℝ) * ((2 * n).choose n : ℝ) / (4 : ℝ) ^ n) ∧
    (∀ n : ℕ, 1 ≤ n →
      expectedSortedDiff n berHalf = (n : ℝ) * ((2 * n).choose n : ℝ) / (4 : ℝ) ^ n) ∧
    (expectedSortedDiff 1 unif01 < expectedSortedDiff 1 berHalf) := by
  sorry

end OMA.S_mo_301135
