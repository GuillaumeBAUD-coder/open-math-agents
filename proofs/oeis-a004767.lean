import OMAStatements.S_oeis_a004767

theorem OMA.solution : type_of% @OMA.S_oeis_a004767.main := by
  intro m hm
  simp only [OMA.S_oeis_a004767.a, Nat.odd_iff] at hm ⊢
  constructor
  · rintro ⟨h1, -⟩
    exact ⟨m / 4, by omega⟩
  · rintro ⟨n, rfl⟩
    omega
