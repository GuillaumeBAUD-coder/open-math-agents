import OMAStatements.S_oeis_a165719

open OMA.S_oeis_a165719 in
/-- `k(k+9) ≡ k(k+1) (mod 8)` vanishes iff `k ≡ 0, 7 (mod 8)`; then the term is `m(8m+9)` or
`(8j+7)(j+2)`, prime only for `m = 1`, giving `17`. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a165719.main := by
  have hmod : ∀ k : ℕ, (8 ∣ k * (k + 9)) ↔ (k % 8 = 0 ∨ k % 8 = 7) := by
    intro k
    rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod]
    have h := Nat.mod_lt k (show 8 > 0 by norm_num)
    interval_cases k % 8 <;> simp
  refine ⟨fun k hk => ?_, fun v => ⟨?_, ?_⟩⟩
  · rw [hmod]
    constructor
    · rintro (h | h)
      · exact ⟨k / 8, by omega, Or.inr (by omega)⟩
      · exact ⟨k / 8 + 1, by omega, Or.inl (by omega)⟩
    · rintro ⟨m, hm, h | h⟩ <;> omega
  · rintro ⟨⟨k, hk, hv⟩, hp⟩
    have h8 : 8 ∣ k * (k + 9) := ⟨v, hv⟩
    rcases (hmod k).mp h8 with h | h
    · obtain ⟨m, rfl⟩ : ∃ m, k = 8 * m := ⟨k / 8, by omega⟩
      have hv' : v = m * (8 * m + 9) := by nlinarith
      subst hv'
      rcases Nat.prime_mul_iff.mp hp with ⟨_, h1⟩ | ⟨_, h1⟩
      · omega
      · subst h1; norm_num
    · obtain ⟨j, rfl⟩ : ∃ j, k = 8 * j + 7 := ⟨k / 8, by omega⟩
      have hv' : v = (8 * j + 7) * (j + 2) := by nlinarith
      subst hv'
      exact absurd hp (Nat.not_prime_mul (by omega) (by omega))
  · rintro rfl
    exact ⟨⟨8, by norm_num, by norm_num⟩, by norm_num⟩
