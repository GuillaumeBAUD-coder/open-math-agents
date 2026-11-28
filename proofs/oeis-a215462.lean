import OMAStatements.S_oeis_a215462

/-! `9`, `25`, `35` are odd nonprimes with residues `0`, `1`, `2` modulo `3`; subtracting the right one from `2n`
leaves an odd multiple of `3` larger than `3`, hence an odd nonprime. -/

theorem OMA.solution : type_of% @OMA.S_oeis_a215462.main := by
  intro n hn
  have key : ∀ a : ℕ, ¬ a.Prime → a % 2 = 1 → a < 2 * n → 3 ∣ 2 * n - a → 3 < 2 * n - a →
      ∃ a b : ℕ, Odd a ∧ Odd b ∧ ¬ a.Prime ∧ ¬ b.Prime ∧ a + b = 2 * n := by
    intro a ha hodd hlt h3 hgt
    refine ⟨a, 2 * n - a, Nat.odd_iff.mpr hodd, Nat.odd_iff.mpr (by omega), ha, ?_, by omega⟩
    intro hb
    have := hb.eq_one_or_self_of_dvd 3 h3
    omega
  rcases (show (2 * n) % 3 = 0 ∨ (2 * n) % 3 = 1 ∨ (2 * n) % 3 = 2 by omega) with h | h | h
  · exact key 9 (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
  · exact key 25 (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
  · exact key 35 (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
