import OMAStatements.S_oeis_a007526

theorem OMA.solution : type_of% @OMA.S_oeis_a007526.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  have h3 : OMA.S_oeis_a007526.a (k + 3) = (k + 3) * (OMA.S_oeis_a007526.a (k + 2) + 1) := rfl
  have h2 : OMA.S_oeis_a007526.a (k + 2) = (k + 2) * (OMA.S_oeis_a007526.a (k + 1) + 1) := rfl
  have h1 : OMA.S_oeis_a007526.a (k + 1) = (k + 1) * (OMA.S_oeis_a007526.a k + 1) := rfl
  rw [h3, h2, h1]
  push_cast
  ring
