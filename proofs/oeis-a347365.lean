import OMAStatements.S_oeis_a347365

theorem OMA.solution : type_of% @OMA.S_oeis_a347365.main := by
  intro n
  have h1 : Odd (6 * n + 1) := ⟨3 * n, by ring⟩
  have h5 : Odd (6 * n + 5) := ⟨3 * n + 2, by ring⟩
  unfold OMA.S_oeis_a347365.a
  rw [h1.neg_one_pow, h5.neg_one_pow]
  push_cast
  constructor <;> omega
