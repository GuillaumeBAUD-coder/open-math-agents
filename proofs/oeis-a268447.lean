import OMAStatements.S_oeis_a268447

open OMA.S_oeis_a268447

theorem OMA.solution : type_of% @OMA.S_oeis_a268447.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  simp only [a, show m + 9 - 1 = m + 8 from rfl, show m + 9 - 8 = m + 1 from rfl,
    show m + 8 - 8 = m from rfl, show 2 * (m + 9) + 1 = 2 * m + 19 from rfl,
    show 2 * (m + 8) + 1 = 2 * m + 17 from rfl, show m + 9 + 10 = m + 19 from rfl,
    show m + 8 + 10 = m + 18 from rfl,
    show (2 * m + 19).factorial = (2 * m + 19) * ((2 * m + 18) * (2 * m + 17).factorial) from rfl,
    show (m + 19).factorial = (m + 19) * (m + 18).factorial from rfl,
    show (m + 1).factorial = (m + 1) * m.factorial from rfl]
  push_cast
  field_simp
  ring
