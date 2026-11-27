import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R2

/-! Split of R2.H2 into the first-moment lower bound and the second-moment upper bound. -/

-- Reduction LennonPittel.lennon_pittel_conjecture.R2.H2.R1 of step LennonPittel.lennon_pittel_conjecture.R2.H2
-- Credit: @tatashbar
-- Both hypotheses are published theorems, from two different papers with independent proofs:
-- H1 is the first-moment lower bound (Pittel 1989), H2 the second-moment upper bound
-- (Lennon–Pittel 2009). The normalization (n+2) log(n+2) avoids small-n cases.

namespace OMA.R_LennonPittel_lennon_pittel_conjecture_R2_H2_R1

/-- First-moment lower bound of order `n log n` (Pittel 1989: `E[S_n] ~ e⁻¹ n ln n`; together with
`E[S_n] ≥ 1` for every `n` this gives a uniform constant). -/
def H1 : Prop := ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
  c * (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)) ≤ StableMarriage.expectedNumStableMatchings n

/-- Second-moment upper bound of order `(n log n)^2` (Lennon–Pittel 2009:
`E[S_n^2] ~ (e⁻² + e⁻³/2) (n ln n)^2`). -/
def H2 : Prop := ∃ K : ℝ, ∀ n : ℕ,
  ∫ p, (StableMarriage.numStableMatchings p : ℝ) ^ 2 ∂(StableMarriage.uniformProfile n).toMeasure ≤
    K * (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)) ^ 2

theorem main : H1 → H2 → OMA.R_LennonPittel_lennon_pittel_conjecture_R2.H2 := by
  rintro ⟨c, hc, hlow⟩ ⟨K, hup⟩
  refine ⟨max K 0 / c ^ 2, fun n => ?_⟩
  set f : ℝ := ((n : ℝ) + 2) * Real.log ((n : ℝ) + 2) with hf
  have hf0 : 0 ≤ f := by
    have h2 : (1 : ℝ) ≤ (n : ℝ) + 2 := by have := n.cast_nonneg (α := ℝ); linarith
    exact mul_nonneg (by positivity) (Real.log_nonneg h2)
  have hcf : 0 ≤ c * f := mul_nonneg hc.le hf0
  have hsq : (c * f) ^ 2 ≤ StableMarriage.expectedNumStableMatchings n ^ 2 :=
    pow_le_pow_left₀ hcf (hlow n) 2
  calc ∫ p, (StableMarriage.numStableMatchings p : ℝ) ^ 2 ∂(StableMarriage.uniformProfile n).toMeasure
      ≤ K * f ^ 2 := hup n
    _ ≤ max K 0 * f ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    _ = max K 0 / c ^ 2 * (c * f) ^ 2 := by field_simp
    _ ≤ max K 0 / c ^ 2 * StableMarriage.expectedNumStableMatchings n ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)

end OMA.R_LennonPittel_lennon_pittel_conjecture_R2_H2_R1
