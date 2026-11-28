import OMAStatements.S_oeis_a155543
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: (1-4X)^-1 = sum 4^n X^n (eq_inv_iff_mul_eq_one), so a(0) = 2 and a(n+1) = 4^(n+1). A090129(2n+2) is the order of 3 mod 2^(2n+2): by LTE (padicValNat.pow_two_sub_pow) v2(3^k-1) = 2+v2(k) for even k, and 3^k-1 = 2 mod 4 for odd k, so the least k is 4^n (n >= 1) and 2 (n = 0).

namespace OMA.P_oeis_a155543

open OMA.S_oeis_a155543 PowerSeries

lemma inv4 : ((1 : PowerSeries ℚ) - 4 * X)⁻¹ = mk (fun n => (4 : ℚ) ^ n) := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
  have e : mk (fun n => (4 : ℚ) ^ n) * (1 - 4 * X) =
      mk (fun n => (4 : ℚ) ^ n) - C 4 * (mk (fun n => (4 : ℚ) ^ n) * X ^ 1) := by
    simp only [map_ofNat]; ring
  rw [e]
  ext n
  simp only [map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_one]
  rcases n with _ | n
  · simp
  · simp [pow_succ]; ring

lemma A081294_eq (n : ℕ) : A081294 (n + 1) = 2 * 4 ^ n := by
  unfold A081294
  rw [inv4]
  have e : (1 - 2 * X : PowerSeries ℚ) * mk (fun n => (4 : ℚ) ^ n) =
      mk (fun n => (4 : ℚ) ^ n) - C 2 * (mk (fun n => (4 : ℚ) ^ n) * X ^ 1) := by
    simp only [map_ofNat]; ring
  rw [e]
  simp only [map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  simp [pow_succ]; ring

lemma A081294_zero : A081294 0 = 1 := by
  unfold A081294
  rw [inv4]
  simp

lemma v2_even (k : ℕ) (hk : k ≠ 0) (he : Even k) : padicValNat 2 (3 ^ k - 1) = 2 + padicValNat 2 k := by
  have h := padicValNat.pow_two_sub_pow (x := 3) (y := 1) (by norm_num) (by norm_num) (by norm_num) hk he
  have h4 : padicValNat 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have h2 : padicValNat 2 2 = 1 := padicValNat_self
  simp only [one_pow, show (3 : ℕ) + 1 = 4 by norm_num, show (3 : ℕ) - 1 = 2 by norm_num, h4, h2] at h
  omega

lemma odd_mod (k : ℕ) (ho : ¬ Even k) : ¬ 4 ∣ 3 ^ k - 1 := by
  obtain ⟨j, rfl⟩ := Nat.not_even_iff_odd.1 ho
  have h9 : 3 ^ (2 * j + 1) % 4 = 3 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
  have hpos : 1 ≤ 3 ^ (2 * j + 1) := Nat.one_le_pow _ _ (by norm_num)
  generalize 3 ^ (2 * j + 1) = t at h9 hpos ⊢
  omega

lemma ord_eq (n : ℕ) (hn : 1 ≤ n) : A090129 (2 * n + 2) = 4 ^ n := by
  unfold A090129
  have h4 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have hev : Even (4 ^ n) := by
    rw [h4]; exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨by positivity, ?_⟩
    have hne : 3 ^ (4 ^ n) - 1 ≠ 0 := by
      have : 1 < 3 ^ (4 ^ n) := Nat.one_lt_pow (by positivity) (by norm_num)
      omega
    rw [padicValNat_dvd_iff_le hne, v2_even _ (by positivity) hev, h4, padicValNat.prime_pow]
    omega
  · rintro k ⟨hk0, hk⟩
    by_contra hlt
    push_neg at hlt
    by_cases he : Even k
    · have hne : 3 ^ k - 1 ≠ 0 := by
        have : 1 < 3 ^ k := Nat.one_lt_pow (by omega) (by norm_num)
        omega
      rw [padicValNat_dvd_iff_le hne, v2_even k (by omega) he] at hk
      have hd : 2 ^ padicValNat 2 k ≤ k := Nat.le_of_dvd hk0 pow_padicValNat_dvd
      have : 2 ^ padicValNat 2 k < 2 ^ (2 * n) := by rw [← h4]; omega
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 this
      omega
    · exact odd_mod k he (dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ 2 * n + 2)) hk)

lemma ord_two : A090129 2 = 2 := by
  unfold A090129
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨by norm_num, by norm_num⟩
  · rintro k ⟨hk0, hk⟩
    by_contra hlt
    push_neg at hlt
    interval_cases k
    norm_num at hk

end OMA.P_oeis_a155543

theorem OMA.solution : type_of% @OMA.S_oeis_a155543.main := by
  intro n
  rcases n with _ | m
  · rw [OMA.S_oeis_a155543.a, OMA.P_oeis_a155543.A081294_zero, OMA.P_oeis_a155543.ord_two]
    norm_num
  · rw [OMA.S_oeis_a155543.a, OMA.P_oeis_a155543.A081294_eq,
      OMA.P_oeis_a155543.ord_eq (m + 1) (by omega)]
    push_cast; ring
