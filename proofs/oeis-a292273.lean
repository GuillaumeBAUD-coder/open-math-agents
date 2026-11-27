import OMAStatements.S_oeis_a292273

theorem OMA.solution : type_of% @OMA.S_oeis_a292273.main := by
  intro n _
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 4 ∧ n = 4 * k + r :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
  have hI : Complex.I ^ (4 * k + r) = Complex.I ^ r := by
    rw [pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
  rw [hI]
  unfold OMA.S_oeis_a292273.a
  interval_cases r
  · have h0 : ArithmeticFunction.moebius (4 * k) = 0 := by
      apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      intro hs
      have := hs 2 ⟨k, by ring⟩
      exact absurd (Nat.isUnit_iff.mp this) (by norm_num)
    have he : ¬ Odd (4 * k) := by
      rw [Nat.not_odd_iff_even]; exact ⟨2 * k, by ring⟩
    simp [h0, he]
  · have he : Odd (4 * k + 1) := ⟨2 * k, by ring⟩
    simp [he]
  · have he : ¬ Odd (4 * k + 2) := by
      rw [Nat.not_odd_iff_even]; exact ⟨2 * k + 1, by ring⟩
    simp [he, pow_two]
  · have he : Odd (4 * k + 3) := ⟨2 * k + 1, by ring⟩
    simp [he, pow_succ]
