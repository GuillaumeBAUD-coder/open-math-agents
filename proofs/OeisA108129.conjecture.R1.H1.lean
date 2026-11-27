import OMAReductions.R_OeisA108129_conjecture_R1

-- Step OeisA108129.conjecture.R1.H1: hypothesis H1 of reduction OeisA108129.conjecture.R1
-- Credit: @tatashbar
-- H1 := OeisA108129.a 254602 = -1

namespace OMA_A108129_H1

lemma covering : ∀ r < 24, ∃ p ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ),
    509203 * 2 ^ r % p = 1 := by
  decide

lemma period : ∀ p ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ), 2 ^ 24 ≡ 1 [MOD p] ∧ 3 ≤ p ∧ p ≤ 241 := by
  decide

theorem not_prime (m : ℕ) (hm : m ≠ 0) : ¬ (509203 * 2 ^ m - 1).Prime := by
  intro hpr
  obtain ⟨p, hpS, hkey⟩ := covering (m % 24) (Nat.mod_lt _ (by norm_num))
  obtain ⟨h24, hp3, hp241⟩ := period p hpS
  have hmod : 509203 * 2 ^ m ≡ 509203 * 2 ^ (m % 24) [MOD p] := by
    have e : 2 ^ m = (2 ^ 24) ^ (m / 24) * 2 ^ (m % 24) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [e]
    have h1 : (2 ^ 24) ^ (m / 24) * 2 ^ (m % 24) ≡ 1 ^ (m / 24) * 2 ^ (m % 24) [MOD p] :=
      (Nat.ModEq.pow (m / 24) h24).mul_right _
    rw [one_pow, one_mul] at h1
    exact h1.mul_left 509203
  have h1p : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  have hdvd : p ∣ 509203 * 2 ^ m - 1 := by
    apply Nat.dvd_of_mod_eq_zero
    apply Nat.sub_mod_eq_zero_of_mod_eq
    unfold Nat.ModEq at hmod
    rw [hmod, hkey, h1p]
  have h2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hm)
  rcases hpr.eq_one_or_self_of_dvd p hdvd with h | h
  · omega
  · omega

end OMA_A108129_H1

theorem OMA.solution : OMA.R_OeisA108129_conjecture_R1.H1 := by
  unfold OMA.R_OeisA108129_conjecture_R1.H1 OeisA108129.a
  rw [if_neg (by norm_num), dif_neg]
  rintro ⟨m, hm, hpr⟩
  have e : 2 * 254602 - 1 = 509203 := by norm_num
  rw [e] at hpr
  exact OMA_A108129_H1.not_prime m hm hpr
