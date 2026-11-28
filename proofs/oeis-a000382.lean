import OMAStatements.S_oeis_a000382

theorem OMA.a000382_key (f : ℕ → ℤ × ℤ × ℤ × ℤ) (h0 : f 0 = (11, 7, 4, 2))
    (hs : ∀ k, f (k + 1) = (2 * (f k).1 - (f k).2.2.2, (f k).1, (f k).2.1, (f k).2.2.1)) (m : ℕ) :
    (f (m + 6)).2.2.2 = (f (m + 5)).2.2.2 + (f (m + 4)).2.2.2 + (f (m + 3)).2.2.2 - 2 := by
  have inv : ∀ k, (f k).1 - (f k).2.1 - (f k).2.2.1 - (f k).2.2.2 = -2 := by
    intro k
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [hs k]; simp only; linarith
  have e6 : (f (m + 6)).2.2.2 = (f (m + 3)).1 := by simp [hs]
  have e5 : (f (m + 5)).2.2.2 = (f (m + 3)).2.1 := by simp [hs]
  have e4 : (f (m + 4)).2.2.2 = (f (m + 3)).2.2.1 := by simp [hs]
  rw [e6, e5, e4]
  linarith [inv (m + 3)]

theorem OMA.solution : type_of% @OMA.S_oeis_a000382.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
    show m + 8 - 3 = m + 5 by omega]
  simp only [OMA.S_oeis_a000382.a]
  split_ifs <;> try omega
  rw [show m + 8 - 2 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 6 - 2 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega]
  exact OMA.a000382_key _ rfl (fun k => rfl) m
