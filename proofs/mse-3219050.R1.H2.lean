import OMAReductions.R_mse_3219050_R1

-- Step mse-3219050.R1.H2: hypothesis H2 of reduction mse-3219050.R1
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
theorem OMA.solution : OMA.R_mse_3219050_R1.H2 := by
  intro n hn hp hq
  by_contra h3
  have h2n : 2 ^ n ≡ 2 [MOD 3] := modEq_two_of_odd n hn
  have hle : n ≤ 2 ^ n := Nat.le_of_lt Nat.lt_two_pow_self
  have hlt : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hne : n % 3 ≠ 0 := by
    intro h
    exact h3 (Nat.dvd_of_mod_eq_zero h)
  have hres : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hres with h1 | h2
  · have hm : n ≡ 1 [MOD 3] := by
      show n % 3 = 1 % 3
      simpa using h1
    have h30 : (3 : ℕ) ≡ 0 [MOD 3] := Nat.modEq_zero_iff_dvd.mpr (dvd_refl 3)
    have hs : 2 ^ n + n ≡ 0 [MOD 3] := (h2n.add hm).trans h30
    have hd : 3 ∣ 2 ^ n + n := Nat.modEq_zero_iff_dvd.mp hs
    rcases hq.eq_one_or_self_of_dvd 3 hd with h | h
    · omega
    · have hn1 : n = 1 := by
        rcases Nat.lt_or_ge n 2 with h' | h'
        · have hpos : n ≠ 0 := by
            rintro rfl
            norm_num at hp
          omega
        · have h4 : 4 ≤ 2 ^ n := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h'
          omega
      subst hn1
      norm_num at hp
  · have hdr : n = 3 * (n / 3) + 2 := by
      have := Nat.div_add_mod n 3
      omega
    have hd2 : 3 ∣ n - 2 := ⟨n / 3, by omega⟩
    have hd2' : 3 ∣ 2 ^ n - 2 := by
      obtain ⟨k, rfl⟩ := hn
      exact three_dvd_pow_odd k
    have hdn : 3 ∣ 2 ^ n - n := by
      have hsub : 3 ∣ (2 ^ n - 2) - (n - 2) := Nat.dvd_sub hd2' hd2
      have heq : (2 ^ n - 2) - (n - 2) = 2 ^ n - n := by omega
      rwa [heq] at hsub
    rcases hp.eq_one_or_self_of_dvd 3 hdn with h | h
    · omega
    · have h3n : 2 ^ n - n = 3 := h.symm
      rcases Nat.lt_or_ge n 3 with h' | h'
      · obtain ⟨k, hk⟩ := hn
        omega
      · have heq : 2 ^ n = n + 3 := by
          have := (Nat.sub_eq_iff_eq_add hle).1 h3n
          omega
        have hkey := pow_bound n h'
        rw [heq] at hkey
        exact absurd hkey (lt_irrefl _)

