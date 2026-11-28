import OMAStatements.S_oeis_a213243
import Mathlib

namespace A213243

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

lemma a_eq (n : ℕ) (hn : n ≠ 0) : OMA.S_oeis_a213243.a n = (2 ^ n - 1) / (2 ^ n - 1).gcd 3 := by
  unfold OMA.S_oeis_a213243.a
  rw [card_pow_image (GaloisField 2 n) 3 (by norm_num), GaloisField.card 2 n hn]

lemma four_pow (k : ℕ) : ∃ t, 4 ^ k = 3 * t + 1 := by
  induction k with
  | zero => exact ⟨0, by norm_num⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨4 * t + 1, by rw [pow_succ, ht]; ring⟩

lemma even_val (k : ℕ) (hk : 0 < k) : 3 * OMA.S_oeis_a213243.a (2 * k) + 1 = 2 ^ (2 * k) := by
  obtain ⟨t, ht⟩ := four_pow k
  have h2 : 2 ^ (2 * k) = 3 * t + 1 := by rw [pow_mul]; exact ht
  rw [a_eq (2 * k) (by omega), h2, Nat.add_sub_cancel, Nat.gcd_eq_right (dvd_mul_right 3 t),
    Nat.mul_div_cancel_left t (by norm_num)]

lemma odd_val (k : ℕ) : OMA.S_oeis_a213243.a (2 * k + 1) + 1 = 2 ^ (2 * k + 1) := by
  obtain ⟨t, ht⟩ := four_pow k
  have e : 2 ^ (2 * k + 1) = 4 ^ k * 2 := by
    rw [pow_succ, pow_mul]
    norm_num
  have h2 : 2 ^ (2 * k + 1) = 6 * t + 1 + 1 := by
    rw [e, ht]
    ring
  have hg : (6 * t + 1).gcd 3 = 1 := by
    have hd : (6 * t + 1).gcd 3 ∣ 3 := Nat.gcd_dvd_right _ _
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact h
    · exfalso
      have h3 : 3 ∣ 6 * t + 1 := by
        have := Nat.gcd_dvd_left (6 * t + 1) 3
        rw [h] at this
        exact this
      omega
  rw [a_eq (2 * k + 1) (by omega), h2, Nat.add_sub_cancel, hg, Nat.div_one]

lemma rec2 (n : ℕ) (hn : 5 ≤ n) : ((OMA.S_oeis_a213243.a n : ℕ) : ℤ) =
    5 * ((OMA.S_oeis_a213243.a (n - 2) : ℕ) : ℤ) - 4 * ((OMA.S_oeis_a213243.a (n - 4) : ℕ) : ℤ) := by
  obtain ⟨k, hk⟩ : ∃ k, n = 2 * (k + 3) ∨ n = 2 * (k + 2) + 1 := ⟨(n - 5) / 2, by omega⟩
  rcases hk with rfl | rfl
  · have h6 := even_val (k + 3) (by omega)
    have h4 := even_val (k + 2) (by omega)
    have h2 := even_val (k + 1) (by omega)
    have e4 : 2 ^ (2 * (k + 2)) = 4 * 2 ^ (2 * (k + 1)) := by ring
    have e6 : 2 ^ (2 * (k + 3)) = 16 * 2 ^ (2 * (k + 1)) := by ring
    rw [show 2 * (k + 3) - 2 = 2 * (k + 2) by omega, show 2 * (k + 3) - 4 = 2 * (k + 1) by omega]
    omega
  · have h5 := odd_val (k + 2)
    have h3 := odd_val (k + 1)
    have h1 := odd_val k
    have e3 : 2 ^ (2 * (k + 1) + 1) = 4 * 2 ^ (2 * k + 1) := by ring
    have e5 : 2 ^ (2 * (k + 2) + 1) = 16 * 2 ^ (2 * k + 1) := by ring
    rw [show 2 * (k + 2) + 1 - 2 = 2 * (k + 1) + 1 by omega,
      show 2 * (k + 2) + 1 - 4 = 2 * k + 1 by omega]
    omega

noncomputable def g (n : ℕ) : ℤ := if n = 0 then 0 else ((OMA.S_oeis_a213243.a n : ℕ) : ℤ)

lemma g_pos (n : ℕ) (hn : n ≠ 0) : g n = ((OMA.S_oeis_a213243.a n : ℕ) : ℤ) := by
  unfold g
  rw [if_neg hn]

lemma coeff_den (f : ℕ → ℤ) (n : ℕ) :
    coeff n (mk f * (C (4 : ℤ) * (X : PowerSeries ℤ) ^ 4 + C (-5 : ℤ) * (X : PowerSeries ℤ) ^ 2 + C (1 : ℤ) * (X : PowerSeries ℤ) ^ 0)) =
    (4 : ℤ) * (if 4 ≤ n then f (n - 4) else 0) + (-5 : ℤ) * (if 2 ≤ n then f (n - 2) else 0) + (1 : ℤ) * (if 0 ≤ n then f (n - 0) else 0) := by
  have e : mk f * (C (4 : ℤ) * (X : PowerSeries ℤ) ^ 4 + C (-5 : ℤ) * (X : PowerSeries ℤ) ^ 2 + C (1 : ℤ) * (X : PowerSeries ℤ) ^ 0) =
      C (4 : ℤ) * (mk f * (X : PowerSeries ℤ) ^ 4) + C (-5 : ℤ) * (mk f * (X : PowerSeries ℤ) ^ 2) + C (1 : ℤ) * (mk f * (X : PowerSeries ℤ) ^ 0) := by
    ring
  rw [e]
  simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]

end A213243

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a213243.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · have h := A213243.even_val k (by omega)
      have hq : (3 : ℚ) * ((OMA.S_oeis_a213243.a (2 * k) : ℕ) : ℚ) + 1 = 2 ^ (2 * k) := by exact_mod_cast h
      have hp : ((-1 : ℚ)) ^ (2 * k) = 1 := by
        rw [pow_mul]
        norm_num
      rw [hp]
      linear_combination (1 / 3 : ℚ) * hq
    · have h := A213243.odd_val k
      have hq : ((OMA.S_oeis_a213243.a (2 * k + 1) : ℕ) : ℚ) + 1 = 2 ^ (2 * k + 1) := by exact_mod_cast h
      have hp : ((-1 : ℚ)) ^ (2 * k + 1) = -1 := by
        rw [pow_succ, pow_mul]
        norm_num
      rw [hp]
      linear_combination hq
  · intro n hn
    exact A213243.rec2 n hn
  · have hden : (((X : PowerSeries ℤ) - 1) * ((X : PowerSeries ℤ) + 1) * (2 * (X : PowerSeries ℤ) - 1)
        * (2 * (X : PowerSeries ℤ) + 1)) =
        C (4 : ℤ) * (X : PowerSeries ℤ) ^ 4 + C (-5 : ℤ) * (X : PowerSeries ℤ) ^ 2 + C (1 : ℤ) * (X : PowerSeries ℤ) ^ 0 := by
      simp only [map_neg, map_one, map_ofNat]
      ring
    have hnum : (X : PowerSeries ℤ) * (2 * (X : PowerSeries ℤ) ^ 2 + (X : PowerSeries ℤ) + 1) =
        C (2 : ℤ) * (X : PowerSeries ℤ) ^ 3 + C (1 : ℤ) * (X : PowerSeries ℤ) ^ 2 + C (1 : ℤ) * (X : PowerSeries ℤ) ^ 1 := by
      simp only [map_one, map_ofNat]
      ring
    have hg : (PowerSeries.mk fun n => if n = 0 then (0 : ℤ) else ((OMA.S_oeis_a213243.a n : ℕ) : ℤ)) =
        PowerSeries.mk A213243.g := rfl
    rw [hg]
    ext n
    rw [hden, hnum, A213243.coeff_den]
    simp only [map_add, coeff_C_mul, coeff_X_pow]
    have g0 : A213243.g 0 = 0 := by simp [A213243.g]
    have g1 : A213243.g 1 = 1 := by
      have h := A213243.odd_val 0
      rw [A213243.g_pos 1 (by norm_num)]
      norm_num at h
      omega
    have g2 : A213243.g 2 = 1 := by
      have h := A213243.even_val 1 (by norm_num)
      rw [A213243.g_pos 2 (by norm_num)]
      norm_num at h
      omega
    have g3 : A213243.g 3 = 7 := by
      have h := A213243.odd_val 1
      rw [A213243.g_pos 3 (by norm_num)]
      norm_num at h
      omega
    have g4 : A213243.g 4 = 5 := by
      have h := A213243.even_val 2 (by norm_num)
      rw [A213243.g_pos 4 (by norm_num)]
      norm_num at h
      omega
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n) with
      rfl | rfl | rfl | rfl | rfl | h5
    · norm_num [g0]
    · norm_num [g1]
    · norm_num [g0, g2]
    · norm_num [g1, g3]
    · norm_num [g0, g2, g4]
    · have h := A213243.rec2 n h5
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), Nat.sub_zero,
        A213243.g_pos (n - 4) (by omega), A213243.g_pos (n - 2) (by omega),
        A213243.g_pos n (by omega)]
      linarith
