import OMAReductions.R_Erdos1002_erdos_1002_R1
import Mathlib

open ProbabilityTheory

theorem OMA.solution : OMA.R_Erdos1002_erdos_1002_R1.H3 := by
  unfold OMA.R_Erdos1002_erdos_1002_R1.H3
  intro γ g
  have e : g = cdf (cauchyMeasure 0 γ) := funext fun c => (cdf_eq_real _ c).symm
  rw [e]
  exact ⟨(cdf _).mono, tendsto_cdf_atBot _, tendsto_cdf_atTop _⟩
