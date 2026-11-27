import OMAStatements.S_oeis_a169597
theorem OMA.solution : type_of% @OMA.S_oeis_a169597.main := by
  intro n _ hm p hp hq h
  obtain rfl : p = 6 * n + 5 := by
    rcases lt_trichotomy p (6 * n + 5) with h' | h' | h' <;> [nlinarith; exact h'; nlinarith]
  rcases hm with hm | hm
  · rcases hq.eq_one_or_self_of_dvd 19 (by omega) with h' | h' <;> omega
  · rcases hp.eq_one_or_self_of_dvd 19 (by omega) with h' | h' <;> omega
