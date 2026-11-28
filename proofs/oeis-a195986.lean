import OMAStatements.S_oeis_a195986

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: for odd n both 5^n - 3^n and 3^n - 1 are 2 mod 4, so a n = b n = 1. For even n the
-- lifting-the-exponent lemma (Mathlib padicValNat.pow_two_sub_pow) gives
-- a n = 3 + v2(n) and b n = 2 + v2(n), so b n ≠ 1 and a n = b n + 1.

namespace OMA.Sol_oeis_a195986

lemma v_of_mod4 (x : ℕ) (h : x % 4 = 2) : padicValNat 2 x = 1 := by
  have hx : x = 2 * (x / 2) := by omega
  have hodd : ¬ 2 ∣ x / 2 := by omega
  rw [hx, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
    padicValNat.eq_zero_of_not_dvd hodd]

end OMA.Sol_oeis_a195986

open OMA.S_oeis_a195986 in
theorem OMA.solution : type_of% @OMA.S_oeis_a195986.main := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hn0 : n ≠ 0 := by omega
    have hev : Even n := ⟨k, hk⟩
    have h1 := padicValNat.pow_two_sub_pow (x := 5) (y := 3) (by norm_num) (by norm_num)
      (by norm_num) hn0 hev
    have h2 := padicValNat.pow_two_sub_pow (x := 3) (y := 1) (by norm_num) (by norm_num)
      (by norm_num) hn0 hev
    simp only [one_pow] at h2
    have e8 : padicValNat 2 (5 + 3) = 3 := by
      rw [show (5 + 3 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
    have e2 : padicValNat 2 (5 - 3) = 1 := by norm_num
    have e4 : padicValNat 2 (3 + 1) = 2 := by
      rw [show (3 + 1 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    have e2' : padicValNat 2 (3 - 1) = 1 := by norm_num
    unfold a b
    rw [e8, e2] at h1
    rw [e4, e2'] at h2
    have hb : padicValNat 2 (3 ^ n - 1) ≠ 1 := by omega
    rw [if_neg hb]
    omega
  · have h5 : 5 ^ n % 4 = 1 := by
      rw [Nat.pow_mod]; norm_num
    have h3 : 3 ^ n % 4 = 3 := by
      rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
    have hlt : 3 ^ n < 5 ^ n := Nat.pow_lt_pow_left (by norm_num) (by omega)
    have h1 : padicValNat 2 (3 ^ n - 1) = 1 :=
      OMA.Sol_oeis_a195986.v_of_mod4 _ (by have := Nat.one_le_pow n 3 (by norm_num); omega)
    unfold a b
    rw [h1, if_pos rfl]
    exact OMA.Sol_oeis_a195986.v_of_mod4 _ (by omega)
