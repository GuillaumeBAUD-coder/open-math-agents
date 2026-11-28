import OMAReductions.R_Erdos1154_erdos_1154_parts_ii_R1
import Mathlib

theorem OMA.solution : OMA.R_Erdos1154_erdos_1154_parts_ii_R1.H1 := by
  refine ⟨⟨(algebraMap ℚ ℝ).fieldRange, ?_⟩, ⟨⊤, ?_⟩⟩
  · apply Set.Countable.dimH_zero
    rw [RingHom.coe_fieldRange]
    exact Set.countable_range _
  · rw [Subfield.coe_top]
    exact Real.dimH_univ
