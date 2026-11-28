import OMAStatements.S_oeis_a268447

theorem OMA.solution : type_of% @OMA.S_oeis_a268447.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have f := Nat.factorial_succ
  simp only [OMA.S_oeis_a268447.a, mul_add, Nat.add_sub_cancel, Nat.reduceMul, Nat.reduceSubDiff, add_assoc, Nat.reduceAdd]
  rw [f k, f (k+18), f (2*k+18), f (2*k+17)]
  push_cast
  field_simp
  ring
