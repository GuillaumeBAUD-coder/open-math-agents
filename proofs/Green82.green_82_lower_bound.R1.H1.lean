import OMAReductions.R_Green82_green_82_lower_bound_R1

/-!
# Asymptotic conversion for Ben Green's Open Problem 82

We prove `OMA.R_Green82_green_82_lower_bound_R1.H1`: for every `c > 0`, there exists
`o =o[atTop] 1` such that eventually
`(log (log n)) ^ (1 - |o n|) ≤ c * log (log n) / log (log (log n))`.
Choosing `o n = log (log (log (log n)) / c) / log (log (log n))` yields `o n → 0`
and exact equality for all sufficiently large `n`.
-/

-- Step Green82.green_82_lower_bound.R1.H1: hypothesis H1 of reduction Green82.green_82_lower_bound.R1
-- Credit: @aliuyar1234

open Filter Real Asymptotics
open scoped Topology

theorem OMA.solution : OMA.R_Green82_green_82_lower_bound_R1.H1 := by
  intro c hc
  let L2 : ℕ → ℝ := fun n => Real.log (Real.log (n : ℝ))
  let L3 : ℕ → ℝ := fun n => Real.log (L2 n)
  let o : ℕ → ℝ := fun n => Real.log (L3 n / c) / L3 n
  have hL2 : Tendsto L2 atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hL3 : Tendsto L3 atTop atTop := Real.tendsto_log_atTop.comp hL2
  have ho_littleO : o =o[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    let M : ℝ := max (max 1 c) (max ((4 / ε) ^ 2) (2 * |Real.log c| / ε))
    filter_upwards [hL3.eventually_gt_atTop M] with n hM
    have hM1 : 1 < L3 n := lt_of_le_of_lt ((le_max_left 1 c).trans (le_max_left _ _)) hM
    have hMc : c < L3 n := lt_of_le_of_lt ((le_max_right 1 c).trans (le_max_left _ _)) hM
    have hMsq : (4 / ε) ^ 2 < L3 n := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hM
    have hMlog : 2 * |Real.log c| / ε < L3 n :=
      lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hM
    have h3_pos : 0 < L3 n := lt_trans zero_lt_one hM1
    have hdiv_gt : 1 < L3 n / c := (one_lt_div hc).mpr hMc
    have ho_pos : 0 < o n := div_pos (Real.log_pos hdiv_gt) h3_pos
    have hsqrt_pos : 0 < Real.sqrt (L3 n) := Real.sqrt_pos.mpr h3_pos
    have hsqrt_ge : 4 / ε ≤ Real.sqrt (L3 n) := by
      have h4 : 0 ≤ 4 / ε := by positivity
      exact (Real.le_sqrt h4 h3_pos.le).mpr hMsq.le
    have hlog_sqrt : Real.log (L3 n) ≤ 2 * Real.sqrt (L3 n) := by
      have h1 : Real.log (Real.sqrt (L3 n)) ≤ Real.sqrt (L3 n) - 1 :=
        Real.log_le_sub_one_of_pos hsqrt_pos
      have h2 : Real.log (L3 n) = Real.log (Real.sqrt (L3 n) * Real.sqrt (L3 n)) := by
        rw [Real.mul_self_sqrt h3_pos.le]
      rw [h2, Real.log_mul hsqrt_pos.ne' hsqrt_pos.ne']
      linarith
    have hterm1 : Real.log (L3 n) / L3 n ≤ ε / 2 := by
      rw [div_le_iff₀ h3_pos]
      have hmul : 2 * Real.sqrt (L3 n) ≤ (ε / 2) * L3 n := by
        have hstep : 4 / ε * Real.sqrt (L3 n) ≤ Real.sqrt (L3 n) * Real.sqrt (L3 n) :=
          mul_le_mul_of_nonneg_right hsqrt_ge hsqrt_pos.le
        rw [Real.mul_self_sqrt h3_pos.le] at hstep
        have hstep2 : 2 * Real.sqrt (L3 n) = (ε / 2) * (4 / ε * Real.sqrt (L3 n)) := by
          field_simp [hε.ne']
          ring
        nlinarith
      exact hlog_sqrt.trans hmul
    have hterm2 : -Real.log c / L3 n ≤ ε / 2 := by
      rw [div_le_iff₀ h3_pos]
      have habs : -Real.log c ≤ |Real.log c| := neg_le_abs (Real.log c)
      have hmul : |Real.log c| ≤ (ε / 2) * L3 n := by
        have h := (div_lt_iff₀ hε).mp hMlog
        linarith
      exact habs.trans hmul
    have ho_eq : o n = Real.log (L3 n) / L3 n + (-Real.log c / L3 n) := by
      change Real.log (L3 n / c) / L3 n = Real.log (L3 n) / L3 n + (-Real.log c / L3 n)
      rw [Real.log_div h3_pos.ne' hc.ne']
      ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ho_pos, abs_of_pos zero_lt_one, mul_one,
      ho_eq]
    linarith
  refine ⟨o, ho_littleO, ?_⟩
  filter_upwards [hL2.eventually_gt_atTop 1, hL3.eventually_gt_atTop (max 1 c)] with n h2_gt h3_gt
  have h2_pos : 0 < L2 n := lt_trans zero_lt_one h2_gt
  have h3_gt_one : 1 < L3 n := lt_of_le_of_lt (le_max_left 1 c) h3_gt
  have h3_gt_c : c < L3 n := lt_of_le_of_lt (le_max_right 1 c) h3_gt
  have h3_pos : 0 < L3 n := lt_trans zero_lt_one h3_gt_one
  have hdiv_gt : 1 < L3 n / c := (one_lt_div hc).mpr h3_gt_c
  have ho_pos : 0 < o n := div_pos (Real.log_pos hdiv_gt) h3_pos
  change (L2 n) ^ (1 - |o n|) ≤ c * L2 n / L3 n
  rw [abs_of_pos ho_pos, Real.rpow_def_of_pos h2_pos]
  have hexp_arg : Real.log (L2 n) * (1 - o n) = L3 n - Real.log (L3 n / c) := by
    have h3_ne : L3 n ≠ 0 := h3_pos.ne'
    change L3 n * (1 - Real.log (L3 n / c) / L3 n) = L3 n - Real.log (L3 n / c)
    field_simp [h3_ne]
  rw [hexp_arg, Real.exp_sub, Real.exp_log h2_pos, Real.exp_log (div_pos h3_pos hc)]
  have heq : L2 n / (L3 n / c) = c * L2 n / L3 n := by
    field_simp [hc.ne', h3_pos.ne']
  exact le_of_eq heq
