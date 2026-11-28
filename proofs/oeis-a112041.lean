import OMAStatements.S_oeis_a112041

theorem OMA.solution : type_of% @OMA.S_oeis_a112041.main := by
  rintro k ⟨h1, h3, h9, h27⟩ hk
  have := h1.eq_one_or_self_of_dvd 2
  have := h3.eq_one_or_self_of_dvd 2
  have := h1.eq_one_or_self_of_dvd 5
  have := h3.eq_one_or_self_of_dvd 5
  have := h9.eq_one_or_self_of_dvd 5
  have := h27.eq_one_or_self_of_dvd 5
  rcases (by omega : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4) with
    h | h | h | h | h <;> rcases Nat.mod_two_eq_zero_or_one k with e | e <;> omega
