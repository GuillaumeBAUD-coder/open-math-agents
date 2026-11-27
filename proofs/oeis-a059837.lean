import OMAStatements.S_oeis_a059837
import Mathlib

-- Problem: oeis-a059837
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P059837
open OMA.S_oeis_a059837

theorem dis : ¬ (type_of% @OMA.S_oeis_a059837.main) := by
  intro h
  have h0 := h 0
  simp only at h0
  have d2 : diagonal 2 = 4 := by decide
  have d1 : diagonal 1 = 1 := by decide
  have d0 : diagonal 0 = 1 := by decide
  rw [d2, d1, d0] at h0
  norm_num at h0

end OMA.P059837

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a059837.main) := OMA.P059837.dis
