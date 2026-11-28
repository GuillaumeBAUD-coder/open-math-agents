import OMAStatements.S_oeis_a100434

open OMA.S_oeis_a100434 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a100434.main) := by
  intro h
  have h0 := (h 0).2.2
  have e1 : c 0 = 1 := by decide
  have e2 : d 0 = 2 := by decide
  have e3 : b 0 = -3 := by decide
  rw [show ((c 0 + d 0 : ℤ) : ℚ) = 3 by rw [e1, e2]; norm_num, e3] at h0
  norm_num at h0
