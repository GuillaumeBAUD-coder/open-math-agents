import OMAStatements.S_oeis_a169599
theorem OMA.solution : type_of% @OMA.S_oeis_a169599.main := by
  intro n _ h p hp hq e
  obtain rfl : p = 6 * n + 5 := by nlinarith
  rcases h with h | h
  · have := hp.eq_one_or_self_of_dvd 29 (by omega); omega
  · have := hq.eq_one_or_self_of_dvd 29 (by omega); omega
