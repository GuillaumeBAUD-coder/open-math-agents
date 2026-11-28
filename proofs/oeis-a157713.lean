import OMAStatements.S_oeis_a157713

open OMA.S_oeis_a157713

theorem OMA.solution : type_of% @OMA.S_oeis_a157713.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp [a, mul_add, Nat.factorial_succ]
  field_simp
  ring
