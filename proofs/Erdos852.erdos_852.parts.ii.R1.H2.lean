import OMAReductions.R_Erdos852_erdos_852_parts_ii_R1
import Mathlib

-- Credit: @LordMike

theorem OMA.solution : OMA.R_Erdos852_erdos_852_parts_ii_R1.H2 := by
  unfold OMA.R_Erdos852_erdos_852_parts_ii_R1.H2
  intro C ε hC hε
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hlog.eventually (Filter.eventually_ge_atTop (C / ε)),
    Filter.eventually_gt_atTop (1:ℝ)] with x hx hx1
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hM : 0 < Real.log (Real.log x) := lt_of_lt_of_le (div_pos hC hε) hx
  have hC' : C ≤ Real.log (Real.log x) * ε := (div_le_iff₀ hε).mp hx
  rw [div_le_iff₀ hM]
  nlinarith
