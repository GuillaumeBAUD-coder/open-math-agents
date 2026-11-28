import OMAStatements.S_oeis_a165719

-- Problem oeis-a165719: (1) for k >= 1, 8 divides k(k+9) exactly when k = 8m - 1 or k = 8m for some m >= 1;
-- (2) the only prime of the form k(k+9)/8 with k >= 1 is 17.
-- Upstream: statements/oeis-a165719.lean (declaration OMA.S_oeis_a165719.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: (1) k(k+9) mod 8 depends only on k mod 8, and it is 0 exactly for the residues 0 and 7.
-- (2) If k = 8m then k(k+9)/8 = m(8m+9), prime only for m = 1, which gives 17. If k = 8m - 1 = 8j + 7 then
-- k(k+9)/8 = (8j+7)(j+2), a product of two factors larger than 1. Conversely 17 = 8 * 17 / 8 with k = 8.

open OMA.S_oeis_a165719

private lemma part1_a165719 (k : ℕ) (hk : 1 ≤ k) :
    (8 ∣ k * (k + 9)) ↔ ∃ m : ℕ, 1 ≤ m ∧ (k = 8 * m - 1 ∨ k = 8 * m) := by
  have h8 : (k * (k + 9)) % 8 = ((k % 8) * (k % 8 + 9)) % 8 := by
    simp [Nat.mul_mod, Nat.add_mod]
  have hr : k % 8 < 8 := Nat.mod_lt k (by norm_num)
  rw [Nat.dvd_iff_mod_eq_zero, h8]
  generalize hkr : k % 8 = r at hr ⊢
  interval_cases r
  all_goals
    constructor
    · intro h
      first
        | exact ⟨k / 8, by omega, Or.inr (by omega)⟩
        | exact ⟨(k + 1) / 8, by omega, Or.inl (by omega)⟩
    · rintro ⟨m, hm, h | h⟩ <;> omega

theorem OMA.solution : type_of% @OMA.S_oeis_a165719.main := by
  refine ⟨part1_a165719, ?_⟩
  intro v
  constructor
  · rintro ⟨⟨k, hk, hv⟩, hprime⟩
    obtain ⟨m, hm, h | h⟩ := (part1_a165719 k hk).mp ⟨v, hv⟩
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have hk' : k = 8 * j + 7 := by omega
      subst hk'
      have hv' : v = (8 * j + 7) * (j + 2) := by
        have h2 : 8 * v = 8 * ((8 * j + 7) * (j + 2)) := by rw [← hv]; ring
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
      rw [hv'] at hprime
      rcases Nat.prime_mul_iff.mp hprime with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
    · subst h
      have hv' : v = m * (8 * m + 9) := by
        have h2 : 8 * v = 8 * (m * (8 * m + 9)) := by rw [← hv]; ring
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
      rw [hv'] at hprime
      rcases Nat.prime_mul_iff.mp hprime with ⟨_, h1⟩ | ⟨_, h1⟩
      · omega
      · subst h1
        rw [hv']
  · rintro rfl
    exact ⟨⟨8, by norm_num, by norm_num⟩, by norm_num⟩
