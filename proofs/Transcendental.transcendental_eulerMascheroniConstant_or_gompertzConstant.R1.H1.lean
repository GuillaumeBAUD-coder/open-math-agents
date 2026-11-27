import OMAReductions.R_Transcendental_transcendental_eulerMascheroniConstant_or_gompertzConstant_R1

-- Step Transcendental.transcendental_eulerMascheroniConstant_or_gompertzConstant.R1.H1: hypothesis H1 of reduction Transcendental.transcendental_eulerMascheroniConstant_or_gompertzConstant.R1
-- Credit: @luciusacarr
-- H1 := HasSum (fun n : ℕ => (-1:ℝ)^(n+1) / (((n:ℝ)+1) * ((n+1).factorial:ℝ)))     (∫ t : ℝ in Ioc 0 1, log t * exp (-t))  /-- Rivoal's E-function value and exp(-1) are algebraically independent. -/

namespace OMAStepTranscH1

open Real MeasureTheory Set

lemma int_log_mul_pow (n : ℕ) :
    (∫ t : ℝ in Ioc 0 1, log t * t ^ n) = -1 / ((n:ℝ) + 1) ^ 2 := by
  have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
  let F : ℝ → ℝ := fun t => t ^ n * (t * log t) / ((n:ℝ) + 1) - t ^ (n+1) / ((n:ℝ) + 1) ^ 2
  have hF : ContinuousOn F (Icc 0 1) := by
    apply Continuous.continuousOn
    have := Real.continuous_mul_log
    fun_prop
  have hderiv : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt F (log x * x ^ n) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have h1 : HasDerivAt (fun t => t ^ (n+1) * log t) ((((n+1:ℕ):ℝ) * x ^ n) * log x + x ^ (n+1) * x⁻¹) x :=
      (hasDerivAt_pow (n+1) x).mul (hasDerivAt_log hx0)
    have h2 : HasDerivAt (fun t => t ^ (n+1)) (((n+1:ℕ):ℝ) * x ^ n) x := hasDerivAt_pow (n+1) x
    have h3 := (h1.div_const ((n:ℝ) + 1)).sub (h2.div_const (((n:ℝ) + 1) ^ 2))
    have hFeq : F = fun t => t ^ (n+1) * log t / ((n:ℝ) + 1) - t ^ (n+1) / ((n:ℝ) + 1) ^ 2 := by
      funext t; simp only [F]; ring
    have e : log x * x ^ n = ((((n+1:ℕ):ℝ) * x ^ n) * log x + x ^ (n+1) * x⁻¹) / ((n:ℝ) + 1)
        - ((n+1:ℕ):ℝ) * x ^ n / ((n:ℝ) + 1) ^ 2 := by
      push_cast
      field_simp
      ring
    rw [hFeq, e]
    exact h3
  have hint : IntervalIntegrable (fun t => log t * t ^ n) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.mul_continuousOn (by fun_prop)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hF hderiv hint
  rw [intervalIntegral.integral_of_le (by norm_num)] at this
  rw [this]
  simp [F]
  field_simp

theorem series_eq : HasSum (fun n : ℕ => (-1:ℝ)^(n+1) / (((n:ℝ)+1) * ((n+1).factorial:ℝ)))
    (∫ t : ℝ in Ioc 0 1, log t * exp (-t)) := by
  have key := hasSum_integral_of_dominated_convergence (μ := volume.restrict (Ioc (0:ℝ) 1))
    (F := fun (n : ℕ) (t : ℝ) => log t * ((-t) ^ n / (n.factorial : ℝ)))
    (f := fun t => log t * exp (-t))
    (fun n t => -log t * (t ^ n / (n.factorial : ℝ)))
    (fun n => by fun_prop)
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hl : log t ≤ 0 := log_nonpos ht.1.le ht.2
      simp only [norm_mul, norm_div, norm_pow, Real.norm_eq_abs]
      rw [abs_neg, abs_of_nonpos hl, abs_of_pos ht.1, Nat.abs_cast])
    (Filter.Eventually.of_forall fun t =>
      ((NormedSpace.expSeries_div_hasSum_exp t).mul_left (-log t)).summable)
    (by
      have : (fun t : ℝ => ∑' n : ℕ, -log t * (t ^ n / (n.factorial : ℝ))) =
          fun t => -log t * exp t := by
        funext t
        rw [((NormedSpace.expSeries_div_hasSum_exp t).mul_left (-log t)).tsum_eq,
          Real.exp_eq_exp_ℝ]
      rw [this]
      have hi : IntervalIntegrable (fun t => -log t * exp t) volume 0 1 :=
        intervalIntegral.intervalIntegrable_log'.neg.mul_continuousOn (by fun_prop)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hi)
    (Filter.Eventually.of_forall fun t => by
      have := (NormedSpace.expSeries_div_hasSum_exp (-t)).mul_left (log t)
      rwa [← Real.exp_eq_exp_ℝ] at this)
  refine (HasSum.congr_fun key ?_)
  intro n
  have : (fun t : ℝ => log t * ((-t) ^ n / (n.factorial : ℝ))) =
      fun t => ((-1:ℝ) ^ n / (n.factorial : ℝ)) * (log t * t ^ n) := by
    funext t; rw [neg_pow]; ring
  simp only [this]
  rw [integral_const_mul, int_log_mul_pow, Nat.factorial_succ]
  push_cast
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end OMAStepTranscH1

theorem OMA.solution : OMA.R_Transcendental_transcendental_eulerMascheroniConstant_or_gompertzConstant_R1.H1 :=
  OMAStepTranscH1.series_eq
