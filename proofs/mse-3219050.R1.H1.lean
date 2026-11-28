import OMAReductions.R_mse_3219050_R1

-- Step mse-3219050.R1.H1: hypothesis H1 of reduction mse-3219050.R1
-- Credit: @Raimo33

namespace OMAStep

lemma three_dvd_pow_odd (k : ℕ) : 3 ∣ 2 ^ (2 * k + 1) - 2 := by
  induction k with
  | zero => norm_num
  | succ m ih =>
    have hexp : 2 ^ (2 * (m + 1) + 1) = 4 * 2 ^ (2 * m + 1) := by
      have h : 2 * (m + 1) + 1 = 2 * m + 1 + 2 := by omega
      rw [h, pow_add]
      ring
    rw [hexp]
    have hP : 2 ≤ 2 ^ (2 * m + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have heq : 4 * 2 ^ (2 * m + 1) - 2 = 4 * (2 ^ (2 * m + 1) - 2) + 6 := by omega
    rw [heq]
    exact Nat.dvd_add (dvd_mul_of_dvd_right ih 4) (by norm_num)

lemma modEq_two_of_odd (n : ℕ) (hn : Odd n) : 2 ^ n ≡ 2 [MOD 3] := by
  obtain ⟨k, rfl⟩ := hn
  have hd := three_dvd_pow_odd k
  have hP : 2 ≤ 2 ^ (2 * k + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ((Nat.modEq_iff_dvd' hP).2 hd).symm

lemma pow_bound (m : ℕ) (hm : 3 ≤ m) : m + 3 < 2 ^ m := by
  induction m with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k
      · norm_num at hm
      · norm_num at hm
      · norm_num
    · have h1 := ih hk
      have hP : 0 < 2 ^ k := pow_pos (by norm_num) k
      rw [pow_succ]
      nlinarith


end OMAStep

open OMAStep in
theorem OMA.solution : OMA.R_mse_3219050_R1.H1 := by
  intro n hn hp hq
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      norm_num at hp
    · exact h
  have h2n : 2 ∣ 2 ^ n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact ⟨2 ^ m, by rw [pow_succ']⟩
  have h2sum : 2 ∣ 2 ^ n + n := Nat.dvd_add h2n (even_iff_two_dvd.mp hn)
  have hbig : 3 ≤ 2 ^ n + n := by
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hnpos
    omega
  rcases hq.eq_one_or_self_of_dvd 2 h2sum with h | h <;> omega

