import OMAStatements.S_oeis_a059145
import Mathlib

open OMA.S_oeis_a059145 PowerSeries

theorem P059145.col (k : ℕ) : collapsed2 k = 9 * padicValNat 2 k + 15 := by
  simp [collapsed2, element, ruler]
  ring

theorem P059145.sumv (N : ℕ) :
    ∑ k ∈ Finset.range N, padicValNat 2 (k + 1) = padicValNat 2 N.factorial := by
  induction N with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
      padicValNat.mul (by positivity) (Nat.factorial_ne_zero m)]
    ring

theorem P059145.dig (m : ℕ) : (Nat.digits 2 (2 ^ m - 1)).sum = m := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [Nat.digits_def' (by norm_num) (by omega)]
    rw [show (2 ^ (k + 1) - 1) % 2 = 1 by omega, show (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 by omega]
    simp [ih]
    ring

theorem P059145.hz (n : ℕ) : (a n : ℤ) = 3 * (-11 + 2 ^ (4 + n) - 3 * n) := by
  have hN : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  have hs : a n = 9 * padicValNat 2 (2 ^ (n + 1) - 1).factorial + 15 * (2 ^ (n + 1) - 1) := by
    unfold a
    simp only [P059145.col, Finset.sum_add_distrib, ← Finset.mul_sum, P059145.sumv]
    simp
    ring
  have hl := sub_one_mul_padicValNat_factorial (p := 2) (2 ^ (n + 1) - 1)
  rw [P059145.dig] at hl
  simp only [show 2 - 1 = 1 by rfl, one_mul] at hl
  rw [hs, hl]
  have hc : ((2 ^ (n + 1) - 1 - (n + 1) : ℕ) : ℤ) = (2 : ℤ) ^ (n + 1) - 1 - (n + 1) := by
    have : ((2 ^ (n + 1) : ℕ) : ℤ) = (2 : ℤ) ^ (n + 1) := by push_cast; ring
    omega
  have hc2 : ((2 ^ (n + 1) - 1 : ℕ) : ℤ) = (2 : ℤ) ^ (n + 1) - 1 := by
    have : ((2 ^ (n + 1) : ℕ) : ℤ) = (2 : ℤ) ^ (n + 1) := by push_cast; ring
    omega
  push_cast
  rw [hc, hc2]
  ring

theorem P059145.hq (n : ℕ) : (a n : ℚ) = 3 * (-11 + 2 ^ (4 + n) - 3 * n) := by
  have := P059145.hz n
  exact_mod_cast this

theorem OMA.solution : type_of% @OMA.S_oeis_a059145.main := by
  refine ⟨P059145.hz, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, show m + 3 - 3 = m by omega]
    rw [P059145.hz, P059145.hz, P059145.hz, P059145.hz]
    push_cast
    ring
  · have hL : (PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (2 * X - 1)) : PowerSeries ℚ) = -(PowerSeries.mk (fun n => (a n : ℚ))) + C (4 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1) - C (5 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) + C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    have hR : (3 * (2 * X - 5) : PowerSeries ℚ) = -(C (15 : ℚ)) + C (6 : ℚ) * X ^ 1 := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
      coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    rcases n with _ | _ | _ | _ | n
    · norm_num [P059145.hq]
    · norm_num [P059145.hq]
    · norm_num [P059145.hq]
    · norm_num [P059145.hq]
    · simp only [show n + 1 + 1 + 1 + 1 = n + 4 by omega]
      simp only [show n + 4 - 1 = n + 3 by omega, show n + 4 - 2 = n + 2 by omega, show n + 4 - 3 = n + 1 by omega]
      try simp only [show (n + 4 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 4 = 1) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 4 = 2) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 4 = 3) = False by simp only [eq_iff_iff, iff_false]; omega, if_false]
      try simp only [show (n + 1 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 2 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 3 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 4 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, if_false]
      try simp only [show 1 ≤ n + 4 by omega, show 2 ≤ n + 4 by omega, show 3 ≤ n + 4 by omega, if_true]
      simp only [P059145.hq]
      push_cast
      ring
