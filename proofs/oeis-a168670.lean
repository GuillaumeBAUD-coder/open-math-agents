import OMAStatements.S_oeis_a168670
theorem OMA.solution : type_of% @OMA.S_oeis_a168670.main := by
  intro n _ h p hp hq e
  obtain rfl : p = 6 * n + 5 := by nlinarith
  rcases h with h | h
  · have := hp.eq_one_or_self_of_dvd 11 (by omega); omega
  · have := hq.eq_one_or_self_of_dvd 11 (by omega); omega
