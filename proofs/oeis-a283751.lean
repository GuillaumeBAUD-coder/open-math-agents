import OMAStatements.S_oeis_a283751

theorem OMA.solution : type_of% @OMA.S_oeis_a283751.main := by
  intro n hn hnp
  set p := n.minFac with hp
  have hpp : p.Prime := Nat.minFac_prime (by omega)
  have hpd : p ∣ n := Nat.minFac_dvd n
  obtain ⟨m, hm⟩ := hpd
  have hp2 : 2 ≤ p := hpp.two_le
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; omega
    · exact h
  have hpm : p ≤ m := by
    have hmn : m ∣ n := ⟨p, by rw [hm]; ring⟩
    have hm1 : m ≠ 1 := by
      rintro rfl
      exact hnp (by rw [hm, mul_one]; exact hpp)
    have := Nat.minFac_le_of_dvd (by omega : 2 ≤ m) hmn
    rw [← hp] at this
    exact this
  unfold OMA.S_oeis_a283751.a
  rcases Nat.lt_or_eq_of_le hpm with hlt | heq
  · -- b = m, digits are [0, p]
    have hmem : m ∈ {b : ℕ | 1 < b ∧ n ∣ Nat.ofDigits (b ^ 2) (Nat.digits b n)} := by
      refine ⟨by omega, ?_⟩
      have hd : Nat.digits m n = [0, p] := by
        have h1 : n = 0 + m * p := by rw [hm]; ring
        rw [h1, Nat.digits_add m (by omega) 0 p (by omega) (Or.inr (by omega)),
          Nat.digits_of_lt m p (by omega) hlt]
      rw [hd]
      refine ⟨m, ?_⟩
      simp only [Nat.ofDigits, hm]
      push_cast
      ring
    calc sInf _ ≤ m := Nat.sInf_le hmem
      _ < n := by rw [hm]; nlinarith
  · -- n = p^2, b = p, digits are [0, 0, 1]
    subst heq
    have hmem : p ∈ {b : ℕ | 1 < b ∧ n ∣ Nat.ofDigits (b ^ 2) (Nat.digits b n)} := by
      refine ⟨by omega, ?_⟩
      have hd : Nat.digits p n = [0, 0, 1] := by
        have h1 : n = 0 + p * (0 + p * 1) := by rw [hm]; ring
        rw [h1, Nat.digits_add p (by omega) 0 _ (by omega) (Or.inr (by simp; omega)),
          Nat.digits_add p (by omega) 0 _ (by omega) (Or.inr (by omega)),
          Nat.digits_of_lt p 1 (by omega) (by omega)]
      rw [hd]
      refine ⟨p ^ 2, ?_⟩
      simp only [Nat.ofDigits, hm]
      push_cast
      ring
    calc sInf _ ≤ p := Nat.sInf_le hmem
      _ < n := by rw [hm]; nlinarith
