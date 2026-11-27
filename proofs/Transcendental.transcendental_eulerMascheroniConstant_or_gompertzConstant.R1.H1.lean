import OMAReductions.R_Transcendental_transcendental_eulerMascheroniConstant_or_gompertzConstant_R1
import Mathlib

-- Step Transcendental.transcendental_eulerMascheroniConstant_or_gompertzConstant.R1.H1: hypothesis H1 of reduction Transcendental.transcendental_eulerMascheroniConstant_or_gompertzConstant.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Set Real MeasureTheory
open scoped Topology

/-! Expand exp(-t) as its power series and integrate term by term on (0, 1], which dominated
convergence allows with the bound |log t| t^n / n!, summing to |log t| exp t. The moment
∫ t^n log t over [0, 1] equals -1/(n+1)^2 by the fundamental theorem of calculus applied to
t^(n+1) log t/(n+1) - t^(n+1)/(n+1)^2, which is continuous at 0 because t log t is. -/

namespace TranscendentalStepH1

theorem pow_log_integral (n : ℕ) :
    (∫ t in (0:ℝ)..1, t ^ n * log t) = -1 / ((n:ℝ)+1)^2 := by
  let F : ℝ → ℝ := fun t => t^(n+1) * log t / ((n:ℝ)+1) - t^(n+1) / ((n:ℝ)+1)^2
  have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hcont : ContinuousOn F (Icc 0 1) := by
    have e : F = fun t => t^n * (t * log t) / ((n:ℝ)+1) - t^(n+1) / ((n:ℝ)+1)^2 := by
      funext t; simp only [F]; ring
    rw [e]
    exact (((continuous_pow n).mul continuous_mul_log).div_const _ |>.sub
      ((continuous_pow (n+1)).div_const _)).continuousOn
  have hderiv : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt F (t ^ n * log t) t := by
    intro t ht
    have h := (((hasDerivAt_pow (n+1) t).mul (hasDerivAt_log ht.1.ne')).div_const ((n:ℝ)+1)).sub
      ((hasDerivAt_pow (n+1) t).div_const (((n:ℝ)+1)^2))
    have h2 : HasDerivAt F ((((n + 1 : ℕ) : ℝ) * t ^ (n + 1 - 1) * log t + t ^ (n + 1) * t⁻¹) /
        ((n:ℝ) + 1) - ((n + 1 : ℕ) : ℝ) * t ^ (n + 1 - 1) / ((n:ℝ) + 1) ^ 2) t := h
    refine h2.congr_deriv ?_
    have := ht.1.ne'
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => t ^ n * log t) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.continuousOn_mul (continuous_pow n).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint]
  simp only [F]
  simp
  field_simp

theorem series_eq : HasSum (fun n : ℕ => (-1:ℝ)^(n+1) / (((n:ℝ)+1) * ((n+1).factorial:ℝ)))
    (∫ t : ℝ in Ioc 0 1, log t * exp (-t)) := by
  have hterm : ∀ n : ℕ, (∫ t in (0:ℝ)..1, log t * ((-t)^n / (n.factorial:ℝ))) =
      (-1:ℝ)^(n+1) / (((n:ℝ)+1) * ((n+1).factorial:ℝ)) := by
    intro n
    have e : (fun t : ℝ => log t * ((-t)^n / (n.factorial:ℝ))) =
        fun t => ((-1:ℝ)^n / (n.factorial:ℝ)) * (t ^ n * log t) := by
      funext t; rw [neg_pow]; ring
    rw [e, intervalIntegral.integral_const_mul, pow_log_integral, Nat.factorial_succ]
    push_cast
    have : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    field_simp
    ring
  have key : HasSum (fun n : ℕ => ∫ t in (0:ℝ)..1, log t * ((-t)^n / (n.factorial:ℝ)))
      (∫ t in (0:ℝ)..1, log t * exp (-t)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n t => |log t| * (t^n / (n.factorial:ℝ)))
    · intro n
      exact (Real.measurable_log.mul ((measurable_neg.pow_const n).div_const _)).aestronglyMeasurable
    · intro n
      refine ae_of_all _ fun t ht => ?_
      have ht0 : 0 < t := by simpa using ht.1
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_neg, abs_of_pos ht0,
        Nat.abs_cast]
    · exact ae_of_all _ fun t _ => (Real.summable_pow_div_factorial t).mul_left _
    · have e : (fun t : ℝ => ∑' n : ℕ, |log t| * (t^n / (n.factorial:ℝ))) =
          fun t => |log t| * exp t := by
        funext t
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      rw [e]
      exact intervalIntegral.intervalIntegrable_log'.abs.mul_continuousOn continuous_exp.continuousOn
    · refine ae_of_all _ fun t _ => ?_
      have h := NormedSpace.expSeries_div_hasSum_exp (-t)
      rw [← Real.exp_eq_exp_ℝ] at h
      exact h.mul_left (log t)
  rw [intervalIntegral.integral_of_le zero_le_one] at key
  simpa only [hterm] using key

end TranscendentalStepH1

theorem OMA.solution : OMA.R_Transcendental_transcendental_eulerMascheroniConstant_or_gompertzConstant_R1.H1 := TranscendentalStepH1.series_eq
