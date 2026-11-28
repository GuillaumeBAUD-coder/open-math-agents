import OMAStatements.S_oeis_a281217

open OMA.S_oeis_a281217

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a281217.main) := by
  intro h
  have h1 := h 1
  have ha : a 1 = 3 := by decide
  rw [ha] at h1
  norm_num at h1
