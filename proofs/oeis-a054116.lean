import OMAStatements.S_oeis_a054116

open OMA.S_oeis_a054116

theorem OMA.solution : type_of% @OMA.S_oeis_a054116.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h k (hk : 2 ≤ k) : a (k + 1) = a k + (k + 1).factorial := by
    rw [a, a, if_neg (by omega), if_neg (by omega), Finset.sum_Icc_succ_top (by omega)]
  show a (m + 4) - _ * a (m + 3) + _ * a (m + 2) = 0
  rw [h (m + 3) (by omega), h (m + 2) (by omega), Nat.factorial_succ (m + 3)]
  push_cast
  ring
