import OMAStatements.S_oeis_a213248
import Mathlib

namespace A213248

open PowerSeries

lemma card_pow_image (F : Type) [Field F] [Finite F] (d : ℕ) (hd : 0 < d) :
    Nat.card {x : F // x ≠ 0 ∧ ∃ y : F, y ^ d = x} =
      (Nat.card F - 1) / (Nat.card F - 1).gcd d := by
  have h1 := IsCyclic.card_powMonoidHom_range (G := Fˣ) d
  have h2 : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  rw [h2] at h1
  rw [← h1]
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨Units.mk0 x.1 x.2.1, by
        obtain ⟨y, hy⟩ := x.2.2
        have hy0 : y ≠ 0 := by
          rintro rfl
          rw [zero_pow hd.ne'] at hy
          exact x.2.1 hy.symm
        exact ⟨Units.mk0 y hy0, Units.ext (by simpa using hy)⟩⟩
      invFun := fun u => ⟨((u.1 : Fˣ) : F), (u.1 : Fˣ).ne_zero, by
        obtain ⟨v, hv⟩ := u.2
        exact ⟨((v : Fˣ) : F), by rw [← hv]; simp⟩⟩
      left_inv := fun x => by simp
      right_inv := fun u => by
        apply Subtype.ext
        apply Units.ext
        simp }

lemma a_eq (n : ℕ) (hn : n ≠ 0) : OMA.S_oeis_a213248.a n = (2 ^ n - 1) / (2 ^ n - 1).gcd 13 := by
  unfold OMA.S_oeis_a213248.a
  rw [card_pow_image (GaloisField 2 n) 13 (by norm_num), GaloisField.card 2 n hn]

lemma pow4096 (k : ℕ) : ∃ t, 4096 ^ k = 13 * t + 1 := by
  induction k with
  | zero => exact ⟨0, by norm_num⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨4096 * t + 315, by rw [pow_succ, ht]; ring⟩

lemma gcd_one (x : ℕ) (hx : ¬ 13 ∣ x) : x.gcd 13 = 1 := by
  have hd : x.gcd 13 ∣ 13 := Nat.gcd_dvd_right _ _
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 13)).mp hd with h | h
  · exact h
  · exfalso
    have h3 : x.gcd 13 ∣ x := Nat.gcd_dvd_left x 13
    rw [h] at h3
    exact hx h3

lemma val0 (k : ℕ) (hk : 0 < k) : 13 * OMA.S_oeis_a213248.a (12 * k) + 1 = 2 ^ (12 * k) := by
  obtain ⟨t, ht⟩ := pow4096 k
  have e : 2 ^ (12 * k) = 4096 ^ k := by
    rw [pow_mul]
    norm_num
  have h2 : 2 ^ (12 * k) = 13 * t + 1 := by rw [e, ht]
  rw [a_eq (12 * k) (by omega), h2, Nat.add_sub_cancel, Nat.gcd_eq_right (dvd_mul_right 13 t),
    Nat.mul_div_cancel_left t (by norm_num)]

lemma val_ne (k r : ℕ) (hr0 : 0 < r) (hr : r < 12) :
    OMA.S_oeis_a213248.a (12 * k + r) + 1 = 2 ^ (12 * k + r) := by
  obtain ⟨t, ht⟩ := pow4096 k
  have e : 2 ^ (12 * k + r) = 4096 ^ k * 2 ^ r := by
    rw [pow_add, pow_mul]
    norm_num
  have h2 : 2 ^ (12 * k + r) = (13 * t + 1) * 2 ^ r := by rw [e, ht]
  have hpos : 0 < (13 * t + 1) * 2 ^ r := by positivity
  have hnd : ¬ 13 ∣ (13 * t + 1) * 2 ^ r - 1 := by
    interval_cases r <;> omega
  rw [a_eq _ (by omega), h2, gcd_one _ hnd, Nat.div_one]
  exact Nat.sub_add_cancel hpos

lemma rec2 (n : ℕ) (hn : 24 < n) : ((OMA.S_oeis_a213248.a n : ℕ) : ℤ) =
    4097 * ((OMA.S_oeis_a213248.a (n - 12) : ℕ) : ℤ) - 4096 * ((OMA.S_oeis_a213248.a (n - 24) : ℕ) : ℤ) := by
  obtain ⟨k, r, hr, hk⟩ : ∃ k r, r < 12 ∧ n = 12 * (k + 2) + r :=
    ⟨n / 12 - 2, n % 12, Nat.mod_lt _ (by norm_num), by omega⟩
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    subst hk
    have h24 := val0 (j + 3) (by omega)
    have h12 := val0 (j + 2) (by omega)
    have h0 := val0 (j + 1) (by omega)
    have e12 : 2 ^ (12 * (j + 2)) = 4096 * 2 ^ (12 * (j + 1)) := by ring
    have e24 : 2 ^ (12 * (j + 3)) = 16777216 * 2 ^ (12 * (j + 1)) := by ring
    rw [show 12 * (j + 1 + 2) + 0 = 12 * (j + 3) by ring,
      show 12 * (j + 3) - 12 = 12 * (j + 2) by omega,
      show 12 * (j + 3) - 24 = 12 * (j + 1) by omega]
    omega
  · subst hk
    have h24 := val_ne (k + 2) r hr0 hr
    have h12 := val_ne (k + 1) r hr0 hr
    have h0 := val_ne k r hr0 hr
    have e12 : 2 ^ (12 * (k + 1) + r) = 4096 * 2 ^ (12 * k + r) := by ring
    have e24 : 2 ^ (12 * (k + 2) + r) = 16777216 * 2 ^ (12 * k + r) := by ring
    rw [show 12 * (k + 2) + r - 12 = 12 * (k + 1) + r by omega,
      show 12 * (k + 2) + r - 24 = 12 * k + r by omega]
    omega

noncomputable def g (n : ℕ) : ℚ := if n = 0 then 0 else ((OMA.S_oeis_a213248.a n : ℕ) : ℚ)

lemma g_pos (n : ℕ) (hn : n ≠ 0) : g n = ((OMA.S_oeis_a213248.a n : ℕ) : ℚ) := by
  unfold g
  rw [if_neg hn]

lemma g0 : g 0 = 0 := by
  simp [g]

lemma g1 : g 1 = 1 := by
  have h := val_ne 0 1 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 1 = 1 := by omega
  rw [g_pos 1 (by norm_num), h']
  norm_num

lemma g2 : g 2 = 3 := by
  have h := val_ne 0 2 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 2 = 3 := by omega
  rw [g_pos 2 (by norm_num), h']
  norm_num

lemma g3 : g 3 = 7 := by
  have h := val_ne 0 3 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 3 = 7 := by omega
  rw [g_pos 3 (by norm_num), h']
  norm_num

lemma g4 : g 4 = 15 := by
  have h := val_ne 0 4 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 4 = 15 := by omega
  rw [g_pos 4 (by norm_num), h']
  norm_num

lemma g5 : g 5 = 31 := by
  have h := val_ne 0 5 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 5 = 31 := by omega
  rw [g_pos 5 (by norm_num), h']
  norm_num

lemma g6 : g 6 = 63 := by
  have h := val_ne 0 6 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 6 = 63 := by omega
  rw [g_pos 6 (by norm_num), h']
  norm_num

lemma g7 : g 7 = 127 := by
  have h := val_ne 0 7 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 7 = 127 := by omega
  rw [g_pos 7 (by norm_num), h']
  norm_num

lemma g8 : g 8 = 255 := by
  have h := val_ne 0 8 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 8 = 255 := by omega
  rw [g_pos 8 (by norm_num), h']
  norm_num

lemma g9 : g 9 = 511 := by
  have h := val_ne 0 9 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 9 = 511 := by omega
  rw [g_pos 9 (by norm_num), h']
  norm_num

lemma g10 : g 10 = 1023 := by
  have h := val_ne 0 10 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 10 = 1023 := by omega
  rw [g_pos 10 (by norm_num), h']
  norm_num

lemma g11 : g 11 = 2047 := by
  have h := val_ne 0 11 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 11 = 2047 := by omega
  rw [g_pos 11 (by norm_num), h']
  norm_num

lemma g12 : g 12 = 315 := by
  have h := val0 1 (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 12 = 315 := by omega
  rw [g_pos 12 (by norm_num), h']
  norm_num

lemma g13 : g 13 = 8191 := by
  have h := val_ne 1 1 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 13 = 8191 := by omega
  rw [g_pos 13 (by norm_num), h']
  norm_num

lemma g14 : g 14 = 16383 := by
  have h := val_ne 1 2 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 14 = 16383 := by omega
  rw [g_pos 14 (by norm_num), h']
  norm_num

lemma g15 : g 15 = 32767 := by
  have h := val_ne 1 3 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 15 = 32767 := by omega
  rw [g_pos 15 (by norm_num), h']
  norm_num

lemma g16 : g 16 = 65535 := by
  have h := val_ne 1 4 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 16 = 65535 := by omega
  rw [g_pos 16 (by norm_num), h']
  norm_num

lemma g17 : g 17 = 131071 := by
  have h := val_ne 1 5 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 17 = 131071 := by omega
  rw [g_pos 17 (by norm_num), h']
  norm_num

lemma g18 : g 18 = 262143 := by
  have h := val_ne 1 6 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 18 = 262143 := by omega
  rw [g_pos 18 (by norm_num), h']
  norm_num

lemma g19 : g 19 = 524287 := by
  have h := val_ne 1 7 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 19 = 524287 := by omega
  rw [g_pos 19 (by norm_num), h']
  norm_num

lemma g20 : g 20 = 1048575 := by
  have h := val_ne 1 8 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 20 = 1048575 := by omega
  rw [g_pos 20 (by norm_num), h']
  norm_num

lemma g21 : g 21 = 2097151 := by
  have h := val_ne 1 9 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 21 = 2097151 := by omega
  rw [g_pos 21 (by norm_num), h']
  norm_num

lemma g22 : g 22 = 4194303 := by
  have h := val_ne 1 10 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 22 = 4194303 := by omega
  rw [g_pos 22 (by norm_num), h']
  norm_num

lemma g23 : g 23 = 8388607 := by
  have h := val_ne 1 11 (by norm_num) (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 23 = 8388607 := by omega
  rw [g_pos 23 (by norm_num), h']
  norm_num

lemma g24 : g 24 = 1290555 := by
  have h := val0 2 (by norm_num)
  norm_num at h
  have h' : OMA.S_oeis_a213248.a 24 = 1290555 := by omega
  rw [g_pos 24 (by norm_num), h']
  norm_num

lemma coeff_den (f : ℕ → ℚ) (n : ℕ) :
    coeff n (mk f * (C (4096 : ℚ) * (X : PowerSeries ℚ) ^ 24 + C (-4097 : ℚ) * (X : PowerSeries ℚ) ^ 12 + C (1 : ℚ) * (X : PowerSeries ℚ) ^ 0)) =
    (4096 : ℚ) * (if 24 ≤ n then f (n - 24) else 0) + (-4097 : ℚ) * (if 12 ≤ n then f (n - 12) else 0) + (1 : ℚ) * (if 0 ≤ n then f (n - 0) else 0) := by
  have e : mk f * (C (4096 : ℚ) * (X : PowerSeries ℚ) ^ 24 + C (-4097 : ℚ) * (X : PowerSeries ℚ) ^ 12 + C (1 : ℚ) * (X : PowerSeries ℚ) ^ 0) =
      C (4096 : ℚ) * (mk f * (X : PowerSeries ℚ) ^ 24) + C (-4097 : ℚ) * (mk f * (X : PowerSeries ℚ) ^ 12) + C (1 : ℚ) * (mk f * (X : PowerSeries ℚ) ^ 0) := by
    ring
  rw [e]
  simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]

end A213248

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a213248.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    exact A213248.rec2 n hn
  · have hcc : constantCoeff (4096 * (X : PowerSeries ℚ) ^ 24 - 4097 * (X : PowerSeries ℚ) ^ 12 + 1)
        ≠ 0 := by
      simp
    rw [PowerSeries.eq_mul_inv_iff_mul_eq hcc]
    have hden : (4096 * (X : PowerSeries ℚ) ^ 24 - 4097 * (X : PowerSeries ℚ) ^ 12 + 1) =
        C (4096 : ℚ) * (X : PowerSeries ℚ) ^ 24 + C (-4097 : ℚ) * (X : PowerSeries ℚ) ^ 12 + C (1 : ℚ) * (X : PowerSeries ℚ) ^ 0 := by
      simp only [map_neg, map_one, map_ofNat]
      ring
    have hnum : (X : PowerSeries ℚ) * (2048 * (X : PowerSeries ℚ) ^ 22 + 3072 * (X : PowerSeries ℚ) ^ 21 + 3584 * (X : PowerSeries ℚ) ^ 20 + 3840 * (X : PowerSeries ℚ) ^ 19 + 3968 * (X : PowerSeries ℚ) ^ 18 + 4032 * (X : PowerSeries ℚ) ^ 17 + 4064 * (X : PowerSeries ℚ) ^ 16 + 4080 * (X : PowerSeries ℚ) ^ 15 + 4088 * (X : PowerSeries ℚ) ^ 14 + 4092 * (X : PowerSeries ℚ) ^ 13 + 4094 * (X : PowerSeries ℚ) ^ 12 + 315 * (X : PowerSeries ℚ) ^ 11 + 2047 * (X : PowerSeries ℚ) ^ 10 + 1023 * (X : PowerSeries ℚ) ^ 9 + 511 * (X : PowerSeries ℚ) ^ 8 + 255 * (X : PowerSeries ℚ) ^ 7 + 127 * (X : PowerSeries ℚ) ^ 6 + 63 * (X : PowerSeries ℚ) ^ 5 + 31 * (X : PowerSeries ℚ) ^ 4 + 15 * (X : PowerSeries ℚ) ^ 3 + 7 * (X : PowerSeries ℚ) ^ 2 + 3 * (X : PowerSeries ℚ) + 1) =
        C (2048 : ℚ) * (X : PowerSeries ℚ) ^ 23 + C (3072 : ℚ) * (X : PowerSeries ℚ) ^ 22 + C (3584 : ℚ) * (X : PowerSeries ℚ) ^ 21 + C (3840 : ℚ) * (X : PowerSeries ℚ) ^ 20 + C (3968 : ℚ) * (X : PowerSeries ℚ) ^ 19 + C (4032 : ℚ) * (X : PowerSeries ℚ) ^ 18 + C (4064 : ℚ) * (X : PowerSeries ℚ) ^ 17 + C (4080 : ℚ) * (X : PowerSeries ℚ) ^ 16 + C (4088 : ℚ) * (X : PowerSeries ℚ) ^ 15 + C (4092 : ℚ) * (X : PowerSeries ℚ) ^ 14 + C (4094 : ℚ) * (X : PowerSeries ℚ) ^ 13 + C (315 : ℚ) * (X : PowerSeries ℚ) ^ 12 + C (2047 : ℚ) * (X : PowerSeries ℚ) ^ 11 + C (1023 : ℚ) * (X : PowerSeries ℚ) ^ 10 + C (511 : ℚ) * (X : PowerSeries ℚ) ^ 9 + C (255 : ℚ) * (X : PowerSeries ℚ) ^ 8 + C (127 : ℚ) * (X : PowerSeries ℚ) ^ 7 + C (63 : ℚ) * (X : PowerSeries ℚ) ^ 6 + C (31 : ℚ) * (X : PowerSeries ℚ) ^ 5 + C (15 : ℚ) * (X : PowerSeries ℚ) ^ 4 + C (7 : ℚ) * (X : PowerSeries ℚ) ^ 3 + C (3 : ℚ) * (X : PowerSeries ℚ) ^ 2 + C (1 : ℚ) * (X : PowerSeries ℚ) ^ 1 := by
      simp only [map_one, map_ofNat]
      ring
    have hg : (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else ((OMA.S_oeis_a213248.a n : ℕ) : ℚ)) =
        PowerSeries.mk A213248.g := rfl
    rw [hg]
    ext n
    rw [hden, hnum, A213248.coeff_den]
    simp only [map_add, coeff_C_mul, coeff_X_pow]
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ 25 ≤ n) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h25
    · norm_num [A213248.g0]
    · norm_num [A213248.g1]
    · norm_num [A213248.g2]
    · norm_num [A213248.g3]
    · norm_num [A213248.g4]
    · norm_num [A213248.g5]
    · norm_num [A213248.g6]
    · norm_num [A213248.g7]
    · norm_num [A213248.g8]
    · norm_num [A213248.g9]
    · norm_num [A213248.g10]
    · norm_num [A213248.g11]
    · norm_num [A213248.g12, A213248.g0]
    · norm_num [A213248.g13, A213248.g1]
    · norm_num [A213248.g14, A213248.g2]
    · norm_num [A213248.g15, A213248.g3]
    · norm_num [A213248.g16, A213248.g4]
    · norm_num [A213248.g17, A213248.g5]
    · norm_num [A213248.g18, A213248.g6]
    · norm_num [A213248.g19, A213248.g7]
    · norm_num [A213248.g20, A213248.g8]
    · norm_num [A213248.g21, A213248.g9]
    · norm_num [A213248.g22, A213248.g10]
    · norm_num [A213248.g23, A213248.g11]
    · norm_num [A213248.g24, A213248.g12, A213248.g0]
    · have h := A213248.rec2 n (by omega)
      have hq : (((OMA.S_oeis_a213248.a n : ℕ) : ℚ)) =
          4097 * ((OMA.S_oeis_a213248.a (n - 12) : ℕ) : ℚ) - 4096 * ((OMA.S_oeis_a213248.a (n - 24) : ℕ) : ℚ) := by
        exact_mod_cast h
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), Nat.sub_zero,
        A213248.g_pos (n - 24) (by omega), A213248.g_pos (n - 12) (by omega),
        A213248.g_pos n (by omega)]
      linarith
