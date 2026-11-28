import OMAStatements.S_oeis_a330724

theorem OMA.solution : type_of% @OMA.S_oeis_a330724.main := by
  have hmul : ∀ p k : ℕ, p.Prime → k ≠ 0 →
      (p * k).primeFactorsList.sum = p + k.primeFactorsList.sum := by
    intro p k hp hk
    rw [(Nat.perm_primeFactorsList_mul hp.ne_zero hk).sum_eq, List.sum_append,
      Nat.primeFactorsList_prime hp, List.sum_singleton]
  have hp : ∀ p : ℕ, p.Prime → p.primeFactorsList.sum = p := by
    intro p hp
    rw [Nat.primeFactorsList_prime hp, List.sum_singleton]
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have h13 : Nat.Prime 13 := by norm_num
  have key : ∀ m : ℕ, 16 ≤ m →
      ∃ k : ℕ, 1 < k ∧ ¬ k.Prime ∧ Nat.Coprime k 6 ∧ k.primeFactorsList.sum = m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      by_cases hle : m ≤ 20
      · interval_cases m
        · exact ⟨5 * 11, by norm_num, by norm_num, by norm_num,
            by rw [hmul 5 11 h5 (by norm_num), hp 11 h11]⟩
        · exact ⟨5 * (5 * 7), by norm_num, by norm_num, by norm_num,
            by rw [hmul 5 _ h5 (by norm_num), hmul 5 7 h5 (by norm_num), hp 7 h7]⟩
        · exact ⟨7 * 11, by norm_num, by norm_num, by norm_num,
            by rw [hmul 7 11 h7 (by norm_num), hp 11 h11]⟩
        · exact ⟨5 * (7 * 7), by norm_num, by norm_num, by norm_num,
            by rw [hmul 5 _ h5 (by norm_num), hmul 7 7 h7 (by norm_num), hp 7 h7]⟩
        · exact ⟨7 * 13, by norm_num, by norm_num, by norm_num,
            by rw [hmul 7 13 h7 (by norm_num), hp 13 h13]⟩
      · obtain ⟨k, hk1, hkp, hkc, hks⟩ := ih (m - 5) (by omega) (by omega)
        refine ⟨5 * k, by omega, ?_, Nat.Coprime.mul (by norm_num) hkc, ?_⟩
        · intro h
          have := h.eq_one_or_self_of_dvd 5 (Dvd.intro k rfl)
          omega
        · rw [hmul 5 k h5 (by omega), hks]
          omega
  intro m hm
  by_cases h16 : 16 ≤ m
  · exact key m h16
  · rcases hm with ⟨⟨r, hr⟩, h⟩ | ⟨⟨r, hr⟩, h⟩
    · have : m = 12 ∨ m = 14 := by omega
      rcases this with rfl | rfl
      · exact ⟨5 * 7, by norm_num, by norm_num, by norm_num,
          by rw [hmul 5 7 h5 (by norm_num), hp 7 h7]⟩
      · exact ⟨7 * 7, by norm_num, by norm_num, by norm_num,
          by rw [hmul 7 7 h7 (by norm_num), hp 7 h7]⟩
    · omega
