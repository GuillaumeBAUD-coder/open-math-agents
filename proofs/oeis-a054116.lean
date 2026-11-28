import OMAStatements.S_oeis_a054116

open OMA.S_oeis_a054116

theorem OMA.solution : type_of% @OMA.S_oeis_a054116.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  simp [a, Finset.sum_Icc_succ_top, Nat.factorial_succ, show m + 4 - 1 = m + 3 from rfl,
    show m + 4 - 2 = m + 2 from rfl] <;> ring
