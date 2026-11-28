import OMAStatements.S_oeis_a215461

/-! One of `2n - 3`, `2n - 5`, `2n - 7` is a multiple of `3` larger than `3`, hence an odd nonprime. -/

theorem OMA.solution : type_of% @OMA.S_oeis_a215461.main := by
  intro n hn
  have key : ∀ p : ℕ, p.Prime → p % 2 = 1 → p < 2 * n → 3 ∣ 2 * n - p → 3 < 2 * n - p →
      ∃ p q : ℕ, Odd p ∧ Odd q ∧ p.Prime ∧ ¬ q.Prime ∧ p + q = 2 * n := by
    intro p hp hodd hlt h3 hgt
    refine ⟨p, 2 * n - p, Nat.odd_iff.mpr hodd, Nat.odd_iff.mpr (by omega), hp, ?_, by omega⟩
    intro hq
    have := hq.eq_one_or_self_of_dvd 3 h3
    omega
  rcases (show (2 * n) % 3 = 0 ∨ (2 * n) % 3 = 1 ∨ (2 * n) % 3 = 2 by omega) with h | h | h
  · exact key 3 Nat.prime_three (by norm_num) (by omega) (by omega) (by omega)
  · exact key 7 (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
  · exact key 5 Nat.prime_five (by norm_num) (by omega) (by omega) (by omega)
