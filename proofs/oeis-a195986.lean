import OMAStatements.S_oeis_a195986

-- Problem: A195986, the 2-adic valuation of 5^n - 3^n in terms of A090740.
-- Credit: @bnb9001

namespace OMA_A195986_Proof

lemma v2_of_mod4 {m : ℕ} (h : m % 4 = 2) : padicValNat 2 m = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
  have hk : ¬ 2 ∣ k := by omega
  rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
    padicValNat.eq_zero_of_not_dvd hk]

end OMA_A195986_Proof

open OMA_A195986_Proof OMA.S_oeis_a195986 in
theorem OMA.solution : type_of% @OMA.S_oeis_a195986.main := by
  intro n hn
  unfold a b
  rcases Nat.even_or_odd n with hev | hodd
  · have hn0 : n ≠ 0 := by omega
    have h1 := padicValNat.pow_two_sub_pow (x := 5) (y := 3) (by norm_num) (by norm_num)
      (by norm_num) hn0 hev
    have h2 := padicValNat.pow_two_sub_one (x := 3) (by norm_num) (by norm_num) hn0 hev
    have v8 : padicValNat 2 (5 + 3) = 3 := by
      rw [show (5 + 3 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
    have v4 : padicValNat 2 (3 + 1) = 2 := by
      rw [show (3 + 1 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    have v2a : padicValNat 2 (5 - 3) = 1 := by norm_num
    have v2b : padicValNat 2 (3 - 1) = 1 := by norm_num
    rw [v8, v2a] at h1
    rw [v4, v2b] at h2
    rw [if_neg (by omega)]
    omega
  · obtain ⟨m, rfl⟩ := hodd
    have h5 : 5 ^ (2 * m + 1) % 4 = 1 := by
      rw [Nat.pow_mod]; norm_num
    have h3 : 3 ^ (2 * m + 1) % 4 = 3 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
    have hle : 3 ^ (2 * m + 1) ≤ 5 ^ (2 * m + 1) := Nat.pow_le_pow_left (by norm_num) _
    have hpos : 1 ≤ 3 ^ (2 * m + 1) := Nat.one_le_pow _ _ (by norm_num)
    have ha : padicValNat 2 (5 ^ (2 * m + 1) - 3 ^ (2 * m + 1)) = 1 := v2_of_mod4 (by omega)
    have hb : padicValNat 2 (3 ^ (2 * m + 1) - 1) = 1 := v2_of_mod4 (by omega)
    rw [ha, hb, if_pos rfl]
