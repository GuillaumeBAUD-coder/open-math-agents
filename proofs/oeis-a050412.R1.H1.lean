import OMAReductions.R_oeis_a050412_R1

-- Step oeis-a050412.R1.H1: hypothesis H1 of reduction oeis-a050412.R1
-- Credit: @Progren
-- Proof that 509203 is a Riesel number via the covering set {3, 5, 7, 13, 17, 241} (mod 24).

lemma riesel_509203_not_prime_of_mod (p d r k : ℕ)
    (hp1 : 1 < p) (hp_lt : p < 509203 * 2 ^ k - 1)
    (h2d : 2 ^ d % p = 1) (hr : 509203 * 2 ^ r % p = 1)
    (hk : k % d = r) :
    ¬ (509203 * 2 ^ k - 1).Prime := by
  have hpow : 2 ^ k % p = 2 ^ r % p := by
    have hkd : k = d * (k / d) + r := by
      have := Nat.div_add_mod k d
      omega
    rw [hkd, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, h2d, one_pow,
      Nat.mod_eq_of_lt hp1, one_mul, Nat.mod_mod]
  have hmul : 509203 * 2 ^ k % p = 1 := by
    rw [Nat.mul_mod, hpow, ← Nat.mul_mod, hr]
  have hdvd : p ∣ 509203 * 2 ^ k - 1 := by
    refine ⟨509203 * 2 ^ k / p, ?_⟩
    have hdiv := Nat.div_add_mod (509203 * 2 ^ k) p
    omega
  intro hprime
  rcases hprime.eq_one_or_self_of_dvd p hdvd with rfl | heq
  · omega
  · omega

theorem OMA.solution : OMA.R_oeis_a050412_R1.H1 := by
  refine ⟨⟨254601, rfl⟩, ?_⟩
  intro k hk1
  have hk2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  have hcov : k % 2 = 0 ∨ k % 4 = 1 ∨ k % 3 = 2 ∨ k % 8 = 7 ∨ k % 12 = 7 ∨ k % 24 = 3 := by
    omega
  rcases hcov with h | h | h | h | h | h
  · exact riesel_509203_not_prime_of_mod 3 2 0 k (by norm_num) (by omega) (by norm_num) (by norm_num) h
  · exact riesel_509203_not_prime_of_mod 5 4 1 k (by norm_num) (by omega) (by norm_num) (by norm_num) h
  · exact riesel_509203_not_prime_of_mod 7 3 2 k (by norm_num) (by omega) (by norm_num) (by norm_num) h
  · exact riesel_509203_not_prime_of_mod 17 8 7 k (by norm_num) (by omega) (by norm_num) (by norm_num) h
  · exact riesel_509203_not_prime_of_mod 13 12 7 k (by norm_num) (by omega) (by norm_num) (by norm_num) h
  · exact riesel_509203_not_prime_of_mod 241 24 3 k (by norm_num) (by omega) (by norm_num) (by norm_num) h
