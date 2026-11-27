import OMAReductions.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1_H1_R1
import Mathlib

/-! Improper tail integral splitting at an intermediate cutoff for the weighted Chebyshev theta kernel. -/

section RobinThetaTailSplit
open Real Finset MeasureTheory

private noncomputable def thetaIntegrand (t : ℝ) : ℝ :=
  ((2 * log t + 1) / (t ^ 3 * (log t) ^ 2)) * Chebyshev.theta t

private lemma measurable_thetaIntegrand : Measurable thetaIntegrand := by
  unfold thetaIntegrand
  exact (((measurable_const.mul Real.measurable_log).add measurable_const).div
    ((measurable_id.pow_const 3).mul (Real.measurable_log.pow_const 2))).mul
    Chebyshev.theta_mono.measurable

private lemma thetaIntegrand_nonneg {t : ℝ} (ht : 3 ≤ t) : 0 ≤ thetaIntegrand t := by
  have ht0 : 0 < t := by linarith
  have hlog : 0 < log t := Real.log_pos (by linarith)
  unfold thetaIntegrand
  exact mul_nonneg (div_nonneg (by positivity) (by positivity)) (Chebyshev.theta_nonneg t)

private lemma thetaIntegrand_le {t : ℝ} (ht : 3 ≤ t) :
    thetaIntegrand t ≤ (3 * (log 4 + 4)) * t ^ (-2 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hexp1 : exp 1 < t := lt_of_lt_of_le exp_one_lt_d9 (by norm_num; linarith)
  have hlog1 : 1 < log t := (lt_log_iff_exp_lt ht0).mpr hexp1
  have hlog_pos : 0 < log t := by linarith
  have hth : Chebyshev.theta t ≤ (log 4 + 4) * t :=
    (Chebyshev.theta_le_psi t).trans (Chebyshev.psi_le_const_mul_self ht0.le)
  have hfrac : (2 * log t + 1) / (t ^ 3 * (log t) ^ 2) ≤ 3 / t ^ 3 := by
    have hnum : 2 * log t + 1 ≤ 3 * log t := by linarith
    have hden : t ^ 3 * log t ≤ t ^ 3 * (log t) ^ 2 := by
      have : log t ≤ (log t) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    calc (2 * log t + 1) / (t ^ 3 * (log t) ^ 2)
        ≤ (3 * log t) / (t ^ 3 * (log t) ^ 2) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (3 * log t) / (t ^ 3 * log t) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 3 / t ^ 3 := by field_simp [hlog_pos.ne']
  have hrpow : t ^ (-2 : ℝ) = 1 / t ^ 2 := by
    rw [rpow_neg ht0.le, rpow_two, one_div]
  unfold thetaIntegrand
  calc ((2 * log t + 1) / (t ^ 3 * (log t) ^ 2)) * Chebyshev.theta t
      ≤ (3 / t ^ 3) * ((log 4 + 4) * t) :=
        mul_le_mul hfrac hth (Chebyshev.theta_nonneg t) (by positivity)
    _ = (3 * (log 4 + 4)) * (1 / t ^ 2) := by field_simp [ht0.ne']
    _ = (3 * (log 4 + 4)) * t ^ (-2 : ℝ) := by rw [hrpow]

private lemma integrableOn_thetaIntegrand {a : ℝ} (ha : 3 ≤ a) :
    IntegrableOn thetaIntegrand (Set.Ioi a) := by
  have ha0 : 0 < a := by linarith
  have hdom : IntegrableOn (fun t : ℝ => (3 * (log 4 + 4)) * t ^ (-2 : ℝ)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha0).const_mul _
  refine hdom.mono' measurable_thetaIntegrand.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht3 : 3 ≤ t := ha.trans (Set.mem_Ioi.mp ht).le
  rw [Real.norm_of_nonneg (thetaIntegrand_nonneg ht3)]
  exact thetaIntegrand_le ht3

theorem OMA.solution : OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1_H1_R1.H4 := by
  intro s b hs hsb
  have hs3 : 3 ≤ s := by linarith
  have hb3 : 3 ≤ b := by linarith
  have hint_s : IntegrableOn thetaIntegrand (Set.Ioi s) := integrableOn_thetaIntegrand hs3
  have hint_b : IntegrableOn thetaIntegrand (Set.Ioi b) := integrableOn_thetaIntegrand hb3
  have hint_ioc : IntegrableOn thetaIntegrand (Set.Ioc s b) :=
    hint_s.mono_set Set.Ioc_subset_Ioi_self
  have hunion : Set.Ioc s b ∪ Set.Ioi b = Set.Ioi s := Set.Ioc_union_Ioi_eq_Ioi hsb
  have hdisj : Disjoint (Set.Ioc s b) (Set.Ioi b) := Set.Ioc_disjoint_Ioi le_rfl
  have heq : (∫ t in Set.Ioi s, thetaIntegrand t) =
      (∫ t in Set.Ioc s b, thetaIntegrand t) + (∫ t in Set.Ioi b, thetaIntegrand t) := by
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioi hint_ioc hint_b]
  unfold thetaIntegrand at heq
  linarith

end RobinThetaTailSplit
