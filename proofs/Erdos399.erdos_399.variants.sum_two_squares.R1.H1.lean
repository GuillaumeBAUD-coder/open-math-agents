import OMAReductions.R_Erdos399_erdos_399_variants_sum_two_squares_R1

-- Credit: @ezrafayet
-- Five primes cover the entire interval from 7 through 100.
theorem OMA.solution : OMA.R_Erdos399_erdos_399_variants_sum_two_squares_R1.H1 := by
  intro n hn hmax
  by_cases h11 : n < 11
  · exact ⟨7, by norm_num, by norm_num, by omega, hn⟩
  by_cases h19 : n < 19
  · exact ⟨11, by norm_num, by norm_num, by omega, by omega⟩
  by_cases h31 : n < 31
  · exact ⟨19, by norm_num, by norm_num, by omega, by omega⟩
  by_cases h59 : n < 59
  · exact ⟨31, by norm_num, by norm_num, by omega, by omega⟩
  exact ⟨59, by norm_num, by norm_num, by omega, by omega⟩
