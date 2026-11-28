import OMAStatements.S_oeis_a087208

theorem OMA.solution : type_of% @OMA.S_oeis_a087208.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have h1 : OMA.S_oeis_a087208.a (k + 3) =
      (k + 3) * (k + 2) * OMA.S_oeis_a087208.a (k + 1) + 1 := rfl
  have h2 : OMA.S_oeis_a087208.a (k + 2) =
      (k + 2) * (k + 1) * OMA.S_oeis_a087208.a k + 1 := rfl
  have hs1 : k + 3 - 1 = k + 2 := by omega
  have hs2 : k + 3 - 2 = k + 1 := by omega
  have hs3 : k + 3 - 3 = k := by omega
  rw [hs1, hs2, hs3, h1, h2]
  push_cast
  ring
