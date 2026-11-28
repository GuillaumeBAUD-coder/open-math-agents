import OMAStatements.S_oeis_a195986
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a195986.main := by
  intro n hn
  unfold OMA.S_oeis_a195986.a OMA.S_oeis_a195986.b
  rcases Nat.even_or_odd n with he | ho
  · -- even exponent: lifting the exponent at 2
    have h1 := padicValNat.pow_two_sub_pow (x := 5) (y := 3) (by norm_num) (by norm_num)
      (by norm_num) (n := n) (by omega) he
    have h2 := padicValNat.pow_two_sub_one (x := 3) (by norm_num) (by norm_num) (n := n)
      (by omega) he
    have e8 : padicValNat 2 (5 + 3) = 3 := by
      rw [show (5 + 3 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
    have e2 : padicValNat 2 (5 - 3) = 1 := by
      rw [show (5 - 3 : ℕ) = 2 by norm_num, padicValNat_self]
    have e4 : padicValNat 2 (3 + 1) = 2 := by
      rw [show (3 + 1 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    have e2' : padicValNat 2 (3 - 1) = 1 := by
      rw [show (3 - 1 : ℕ) = 2 by norm_num, padicValNat_self]
    rw [e8, e2] at h1
    rw [e4, e2'] at h2
    have hb : ¬ (padicValNat 2 (3 ^ n - 1) = 1) := by omega
    rw [if_neg hb]
    omega
  · -- odd exponent: both numbers are 2 mod 4
    have v : ∀ m : ℕ, m % 4 = 2 → padicValNat 2 m = 1 := by
      intro m hm
      obtain ⟨j, rfl⟩ : ∃ j, m = 2 * (2 * j + 1) := ⟨m / 4, by omega⟩
      rw [padicValNat.mul (by norm_num) (by omega), padicValNat_self,
        padicValNat.eq_zero_of_not_dvd (by omega)]
    obtain ⟨t, rfl⟩ := ho
    have h5 : 5 ^ (2 * t + 1) % 4 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have h3 : 3 ^ (2 * t + 1) % 4 = 3 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have hle : 3 ^ (2 * t + 1) ≤ 5 ^ (2 * t + 1) := Nat.pow_le_pow_left (by norm_num) _
    have hpos : 1 ≤ 3 ^ (2 * t + 1) := Nat.one_le_pow _ _ (by norm_num)
    have ha := v (5 ^ (2 * t + 1) - 3 ^ (2 * t + 1)) (by omega)
    have hb := v (3 ^ (2 * t + 1) - 1) (by omega)
    rw [ha, hb]
    simp
