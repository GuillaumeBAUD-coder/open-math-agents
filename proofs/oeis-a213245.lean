import OMAStatements.S_oeis_a213245
import Mathlib

namespace A213245

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

lemma a_eq (n : ℕ) (hn : n ≠ 0) : OMA.S_oeis_a213245.a n = (2 ^ n - 1) / (2 ^ n - 1).gcd 7 := by
  unfold OMA.S_oeis_a213245.a
  rw [card_pow_image (GaloisField 2 n) 7 (by norm_num), GaloisField.card 2 n hn]

lemma eight_pow (k : ℕ) : ∃ t, 8 ^ k = 7 * t + 1 := by
  induction k with
  | zero => exact ⟨0, by norm_num⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨8 * t + 1, by rw [pow_succ, ht]; ring⟩

lemma gcd_one (x : ℕ) (hx : ¬ 7 ∣ x) : x.gcd 7 = 1 := by
  have hd : x.gcd 7 ∣ 7 := Nat.gcd_dvd_right _ _
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hd with h | h
  · exact h
  · exfalso
    have h3 : x.gcd 7 ∣ x := Nat.gcd_dvd_left x 7
    rw [h] at h3
    exact hx h3

lemma val0 (k : ℕ) (hk : 0 < k) : 7 * OMA.S_oeis_a213245.a (3 * k) + 1 = 2 ^ (3 * k) := by
  obtain ⟨t, ht⟩ := eight_pow k
  have e : 2 ^ (3 * k) = 8 ^ k := by
    rw [pow_mul]
    norm_num
  have h2 : 2 ^ (3 * k) = 7 * t + 1 := by rw [e, ht]
  rw [a_eq (3 * k) (by omega), h2, Nat.add_sub_cancel, Nat.gcd_eq_right (dvd_mul_right 7 t),
    Nat.mul_div_cancel_left t (by norm_num)]

lemma val1 (k : ℕ) : OMA.S_oeis_a213245.a (3 * k + 1) + 1 = 2 ^ (3 * k + 1) := by
  obtain ⟨t, ht⟩ := eight_pow k
  have e : 2 ^ (3 * k + 1) = 8 ^ k * 2 := by
    rw [pow_succ, pow_mul]
    norm_num
  have h2 : 2 ^ (3 * k + 1) = 14 * t + 1 + 1 := by
    rw [e, ht]
    ring
  rw [a_eq (3 * k + 1) (by omega), h2, Nat.add_sub_cancel, gcd_one _ (by omega), Nat.div_one]

lemma val2 (k : ℕ) : OMA.S_oeis_a213245.a (3 * k + 2) + 1 = 2 ^ (3 * k + 2) := by
  obtain ⟨t, ht⟩ := eight_pow k
  have e : 2 ^ (3 * k + 2) = 8 ^ k * 4 := by
    rw [pow_add, pow_mul]
    norm_num
  have h2 : 2 ^ (3 * k + 2) = 28 * t + 3 + 1 := by
    rw [e, ht]
    ring
  rw [a_eq (3 * k + 2) (by omega), h2, Nat.add_sub_cancel, gcd_one _ (by omega), Nat.div_one]

lemma rec2 (n : ℕ) (hn : 7 ≤ n) : ((OMA.S_oeis_a213245.a n : ℕ) : ℤ) =
    9 * ((OMA.S_oeis_a213245.a (n - 3) : ℕ) : ℤ) - 8 * ((OMA.S_oeis_a213245.a (n - 6) : ℕ) : ℤ) := by
  obtain ⟨k, hk⟩ : ∃ k, n = 3 * (k + 3) ∨ n = 3 * (k + 2) + 1 ∨ n = 3 * (k + 2) + 2 :=
    ⟨(n - 7) / 3, by omega⟩
  rcases hk with rfl | rfl | rfl
  · have h6 := val0 (k + 3) (by omega)
    have h3 := val0 (k + 2) (by omega)
    have h0 := val0 (k + 1) (by omega)
    have e3 : 2 ^ (3 * (k + 2)) = 8 * 2 ^ (3 * (k + 1)) := by ring
    have e6 : 2 ^ (3 * (k + 3)) = 64 * 2 ^ (3 * (k + 1)) := by ring
    rw [show 3 * (k + 3) - 3 = 3 * (k + 2) by omega, show 3 * (k + 3) - 6 = 3 * (k + 1) by omega]
    omega
  · have h6 := val1 (k + 2)
    have h3 := val1 (k + 1)
    have h0 := val1 k
    have e3 : 2 ^ (3 * (k + 1) + 1) = 8 * 2 ^ (3 * k + 1) := by ring
    have e6 : 2 ^ (3 * (k + 2) + 1) = 64 * 2 ^ (3 * k + 1) := by ring
    rw [show 3 * (k + 2) + 1 - 3 = 3 * (k + 1) + 1 by omega,
      show 3 * (k + 2) + 1 - 6 = 3 * k + 1 by omega]
    omega
  · have h6 := val2 (k + 2)
    have h3 := val2 (k + 1)
    have h0 := val2 k
    have e3 : 2 ^ (3 * (k + 1) + 2) = 8 * 2 ^ (3 * k + 2) := by ring
    have e6 : 2 ^ (3 * (k + 2) + 2) = 64 * 2 ^ (3 * k + 2) := by ring
    rw [show 3 * (k + 2) + 2 - 3 = 3 * (k + 1) + 2 by omega,
      show 3 * (k + 2) + 2 - 6 = 3 * k + 2 by omega]
    omega

noncomputable def g (n : ℕ) : ℤ := if n = 0 then 0 else ((OMA.S_oeis_a213245.a n : ℕ) : ℤ)

lemma g_pos (n : ℕ) (hn : n ≠ 0) : g n = ((OMA.S_oeis_a213245.a n : ℕ) : ℤ) := by
  unfold g
  rw [if_neg hn]

lemma coeff_den (f : ℕ → ℤ) (n : ℕ) :
    coeff n (mk f * (C (8 : ℤ) * (X : PowerSeries ℤ) ^ 6 + C (-9 : ℤ) * (X : PowerSeries ℤ) ^ 3 + C (1 : ℤ) * (X : PowerSeries ℤ) ^ 0)) =
    (8 : ℤ) * (if 6 ≤ n then f (n - 6) else 0) + (-9 : ℤ) * (if 3 ≤ n then f (n - 3) else 0) + (1 : ℤ) * (if 0 ≤ n then f (n - 0) else 0) := by
  have e : mk f * (C (8 : ℤ) * (X : PowerSeries ℤ) ^ 6 + C (-9 : ℤ) * (X : PowerSeries ℤ) ^ 3 + C (1 : ℤ) * (X : PowerSeries ℤ) ^ 0) =
      C (8 : ℤ) * (mk f * (X : PowerSeries ℤ) ^ 6) + C (-9 : ℤ) * (mk f * (X : PowerSeries ℤ) ^ 3) + C (1 : ℤ) * (mk f * (X : PowerSeries ℤ) ^ 0) := by
    ring
  rw [e]
  simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]

end A213245

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a213245.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    exact A213245.rec2 n hn
  · have hden : (((X : PowerSeries ℤ) - 1) * (2 * (X : PowerSeries ℤ) - 1)
        * ((X : PowerSeries ℤ) ^ 2 + (X : PowerSeries ℤ) + 1)
        * (4 * (X : PowerSeries ℤ) ^ 2 + 2 * (X : PowerSeries ℤ) + 1)) =
        C (8 : ℤ) * (X : PowerSeries ℤ) ^ 6 + C (-9 : ℤ) * (X : PowerSeries ℤ) ^ 3 + C (1 : ℤ) * (X : PowerSeries ℤ) ^ 0 := by
      simp only [map_neg, map_one, map_ofNat]
      ring
    have hnum : (X : PowerSeries ℤ) * (4 * (X : PowerSeries ℤ) ^ 4 + 6 * (X : PowerSeries ℤ) ^ 3
        + (X : PowerSeries ℤ) ^ 2 + 3 * (X : PowerSeries ℤ) + 1) =
        C (4 : ℤ) * (X : PowerSeries ℤ) ^ 5 + C (6 : ℤ) * (X : PowerSeries ℤ) ^ 4 + C (1 : ℤ) * (X : PowerSeries ℤ) ^ 3 + C (3 : ℤ) * (X : PowerSeries ℤ) ^ 2 + C (1 : ℤ) * (X : PowerSeries ℤ) ^ 1 := by
      simp only [map_one, map_ofNat]
      ring
    have hg : (PowerSeries.mk fun n => if n = 0 then (0 : ℤ) else ((OMA.S_oeis_a213245.a n : ℕ) : ℤ)) =
        PowerSeries.mk A213245.g := rfl
    rw [hg]
    ext n
    rw [hden, hnum, A213245.coeff_den]
    simp only [map_add, coeff_C_mul, coeff_X_pow]
    have g0 : A213245.g 0 = 0 := by simp [A213245.g]
    have g1 : A213245.g 1 = 1 := by
      have h := A213245.val1 0
      rw [A213245.g_pos 1 (by norm_num)]
      norm_num at h
      omega
    have g2 : A213245.g 2 = 3 := by
      have h := A213245.val2 0
      rw [A213245.g_pos 2 (by norm_num)]
      norm_num at h
      omega
    have g3 : A213245.g 3 = 1 := by
      have h := A213245.val0 1 (by norm_num)
      rw [A213245.g_pos 3 (by norm_num)]
      norm_num at h
      omega
    have g4 : A213245.g 4 = 15 := by
      have h := A213245.val1 1
      rw [A213245.g_pos 4 (by norm_num)]
      norm_num at h
      omega
    have g5 : A213245.g 5 = 31 := by
      have h := A213245.val2 1
      rw [A213245.g_pos 5 (by norm_num)]
      norm_num at h
      omega
    have g6 : A213245.g 6 = 9 := by
      have h := A213245.val0 2 (by norm_num)
      rw [A213245.g_pos 6 (by norm_num)]
      norm_num at h
      omega
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ 7 ≤ n) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | h7
    · norm_num [g0]
    · norm_num [g1]
    · norm_num [g2]
    · norm_num [g0, g3]
    · norm_num [g1, g4]
    · norm_num [g2, g5]
    · norm_num [g0, g3, g6]
    · have h := A213245.rec2 n h7
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), Nat.sub_zero,
        A213245.g_pos (n - 6) (by omega), A213245.g_pos (n - 3) (by omega),
        A213245.g_pos n (by omega)]
      linarith
