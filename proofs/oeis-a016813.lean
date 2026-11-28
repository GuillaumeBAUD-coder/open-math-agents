import OMAStatements.S_oeis_a016813

theorem OMA.solution : type_of% @OMA.S_oeis_a016813.main := by
  intro m hm
  rw [Nat.odd_iff] at hm
  rw [Nat.even_iff]
  constructor
  · intro h
    exact ⟨m / 4, by unfold OMA.S_oeis_a016813.a; omega⟩
  · rintro ⟨n, rfl⟩
    unfold OMA.S_oeis_a016813.a
    omega
