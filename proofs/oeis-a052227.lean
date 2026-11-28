import OMAStatements.S_oeis_a052227

open OMA.S_oeis_a052227

private theorem a_factorials (n : ℕ) :
    a n = (4 * n + 1) * ((3 * n).factorial : ℚ) /
      (n.factorial * (2 * n + 1).factorial) := by
  unfold a
  rw [Nat.cast_choose ℚ (show n ≤ 3 * n by omega),
    show 3 * n - n = 2 * n by omega, Nat.factorial_succ]
  push_cast
  field_simp

theorem OMA.solution : type_of% @OMA.S_oeis_a052227.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  simp only [a_factorials, Nat.mul_add, Nat.add_assoc]
  simp only [Nat.factorial, Nat.cast_mul, Nat.cast_succ]
  field_simp
  ring
