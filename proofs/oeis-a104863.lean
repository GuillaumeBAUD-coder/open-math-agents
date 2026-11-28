import OMAStatements.S_oeis_a104863

open OMA.S_oeis_a104863

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a104863.main) := by
  intro h
  have h17 := h 17 (by norm_num)
  have h13 : a 13 = 358 := by decide +kernel
  have h15 : a 15 = 578 := by decide +kernel
  have h17v : a 17 = 935 := by decide +kernel
  have e1 : 17 - 2 = 15 := by norm_num
  have e2 : 17 - 4 = 13 := by norm_num
  rw [e1, e2, h13, h15, h17v] at h17
  norm_num at h17
