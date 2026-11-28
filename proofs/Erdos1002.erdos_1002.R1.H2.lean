import OMAReductions.R_Erdos1002_erdos_1002_R1

/-!
# Step H2 of `Erdos1002.erdos_1002.R1`: Lévy transport (direct form)

Write `μ n` for the law of `α ↦ f α n` under Lebesgue measure restricted to `(0,1)` and
`γ = (2π)⁻¹`. Lévy's continuity theorem (`ProbabilityMeasure.tendsto_iff_tendsto_charFun`) turns
pointwise convergence of `charFun (μ n)` to `charFun (cauchyMeasure 0 γ)` into weak convergence
of `μ n` to `cauchyMeasure 0 γ`. As `γ ≠ 0`, that limit has a density, so the frontier `{c}` of
`Iic c` is null, and the Portmanteau theorem
(`ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'`) gives convergence of
`μ n (Iic c)`. No explicit formula for the Cauchy law is needed.

Proof by Claude Opus 5.5; the Lévy and Portmanteau pattern follows Gemini 4 Neon's `e1002_h1`.
-/

open Filter MeasureTheory Set
open scoped Topology NNReal

namespace E1002R1H2D

/-- Measurability of `α ↦ f α n` (G4b). -/
theorem measurable_rotationSum (n : ℕ) :
    Measurable (fun α : ℝ =>
      (1 / Real.log n) * ∑ k ∈ Finset.Icc (1 : ℕ) n, (1 / 2 - Int.fract (α * k))) := by
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ (fun k _ => ?_)
  exact measurable_const.sub (measurable_id.mul_const _).fract

/-- Lévy transport for laws under the uniform measure on `(0,1)` with a nondegenerate Cauchy
limit: convergence of characteristic functions gives convergence of the distribution functions
at every threshold. -/
theorem levy_transport (Y : ℕ → ℝ → ℝ) (hY : ∀ n, Measurable (Y n)) (γ : ℝ≥0) (hγ : γ ≠ 0)
    (h : ∀ t : ℝ, Tendsto (fun n : ℕ => charFun ((volume.restrict (Ioo (0 : ℝ) 1)).map (Y n)) t)
      atTop (𝓝 (charFun (ProbabilityTheory.cauchyMeasure 0 γ) t))) (c : ℝ) :
    Tendsto (fun n : ℕ => (((volume.restrict (Ioo (0 : ℝ) 1)).map (Y n)) (Iic c)).toReal)
      atTop (𝓝 (((ProbabilityTheory.cauchyMeasure 0 γ) (Iic c)).toReal)) := by
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Ioo]⟩
  let μ : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨(volume.restrict (Ioo (0 : ℝ) 1)).map (Y n),
      Measure.isProbabilityMeasure_map (hY n).aemeasurable⟩
  let μ₀ : ProbabilityMeasure ℝ := ⟨ProbabilityTheory.cauchyMeasure 0 γ, inferInstance⟩
  have hweak : Tendsto μ atTop (𝓝 μ₀) := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr h
  have hnull : (μ₀ : Measure ℝ) (frontier (Iic c)) = 0 := by
    rw [frontier_Iic]
    change ProbabilityTheory.cauchyMeasure 0 γ {c} = 0
    rw [ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 hγ]
    exact withDensity_absolutelyContinuous _ _ Real.volume_singleton
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak hnull)

end E1002R1H2D

/-- Step H2 of `Erdos1002.erdos_1002.R1`. -/
theorem OMA.solution : OMA.R_Erdos1002_erdos_1002_R1.H2 := by
  unfold OMA.R_Erdos1002_erdos_1002_R1.H2
  intro f γ hchar c
  have hγ : γ ≠ 0 := by
    intro h
    have h1 : ((γ : ℝ≥0) : ℝ) = (2 * Real.pi)⁻¹ := rfl
    rw [h, NNReal.coe_zero] at h1
    have hpos : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
    exact hpos.ne' h1.symm
  exact E1002R1H2D.levy_transport (fun n α => f α n)
    (fun n => E1002R1H2D.measurable_rotationSum n) γ hγ hchar c
