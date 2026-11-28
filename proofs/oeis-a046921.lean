import OMAStatements.S_oeis_a046921

-- Disproof at n = 2888, i.e. 2n + 1 = 5777 (T. D. Noe, OEIS A046921: the only zero terms appear
-- to be at 5777 and 5993). For every a <= 53, 5777 - 2 a^2 is neither 1 nor prime.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a046921.main) := by
  intro h
  obtain ⟨p, a, hp, heq⟩ := h 2888
  have hp' : p = 5777 - 2 * a ^ 2 := by omega
  have ha : a ≤ 53 := by nlinarith
  subst hp'
  interval_cases a <;> norm_num at hp
