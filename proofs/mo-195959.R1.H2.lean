import OMAReductions.R_mo_195959_R1
import Mathlib

/-! For a finite measure on `[0, ∞)`, `∫ exp (-x t) dμ → μ([0, ∞))` as `t → 0⁺`, by dominated
convergence with the constant bound `1`. -/

namespace OMA.Step_mo_195959_R1_H2

open MeasureTheory Filter Set
open scoped Topology NNReal

theorem laplace_mass (μ : Measure ℝ≥0) (hμ : IsFiniteMeasure μ) :
    Tendsto (fun t : ℝ => ∫ x : ℝ≥0, Real.exp (-(x:ℝ)*t) ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ _ : ℝ≥0, (1:ℝ) ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · exact Eventually.of_forall fun t =>
      (Real.continuous_exp.comp ((NNReal.continuous_coe.neg).mul continuous_const)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with t ht
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have : (0:ℝ) ≤ (x:ℝ) * t := mul_nonneg x.2 (le_of_lt ht)
    linarith
  · exact integrable_const 1
  · refine Eventually.of_forall fun x => ?_
    have hc : Continuous fun t : ℝ => Real.exp (-(x:ℝ)*t) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have := hc.tendsto 0
    simp only [mul_zero, Real.exp_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
end OMA.Step_mo_195959_R1_H2

theorem OMA.solution : OMA.R_mo_195959_R1.H2 :=
  fun μ hμ => OMA.Step_mo_195959_R1_H2.laplace_mass μ hμ
