import OMAStatements.S_oeis_a087208

open OMA.S_oeis_a087208 in
theorem OMA.solution : type_of% @OMA.S_oeis_a087208.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp [a]
  ring
