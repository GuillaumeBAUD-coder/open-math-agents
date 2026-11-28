import OMAStatements.S_oeis_a320047
import Mathlib

namespace OMA.Helpers

open Polynomial OMA.S_oeis_a320047

theorem a320047_P_form (l : ℕ) :
    P l = C ((l : ℚ) - l * (l + 1) * (2 * l + 1)) + C (3 * (l : ℚ) * (l + 1)) * X := by
  induction l with
  | zero => simp [P]
  | succ l ih =>
    have hs : P (l + 1) = P l + ∑ j ∈ Finset.range 2,
        C (R j) * C ((l + 1 : ℕ) : ℚ) ^ j * (X - C ((l + 1 : ℕ) : ℚ)) ^ j := by
      unfold P
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hs, ih]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, R]
    simp only [pow_zero, pow_one, mul_one, zero_add, if_true, one_ne_zero, if_false]
    push_cast
    simp only [map_add, map_sub, map_mul, map_one, map_natCast, C_ofNat]
    ring

theorem a320047_U0 (l : ℕ) : U l 0 = (l : ℚ) * (l + 1) * (2 * l + 1) - l := by
  unfold U
  rw [a320047_P_form]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, if_true, zero_ne_one, if_false, add_zero]
  ring

theorem a320047_U1 (l : ℕ) : U l 1 = 3 * (l : ℚ) * (l + 1) := by
  unfold U
  rw [a320047_P_form]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, if_true, one_ne_zero, if_false, zero_add]
  ring

noncomputable def a320047F (n : ℕ) : ℚ :=
  (4 - 4 * (-1) ^ n - 3 * (-5 + (-1) ^ n) * (n : ℚ) -
      3 * (-3 + (-1) ^ n) * (n : ℚ) ^ 2 + (1 + (-1) ^ (1 + n)) * (n : ℚ) ^ 3) / 8

theorem a320047_closed (n : ℕ) (hn : 0 < n) : a n = a320047F n := by
  unfold a320047F
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have h1 : (2 * (m + 1)) % 2 = 0 := by omega
    have h2 : 2 * (m + 1) / 2 = m + 1 := by omega
    simp only [a, h1, h2, zero_ne_one, if_false, a320047_U1]
    have e1 : ((-1 : ℚ)) ^ (2 * (m + 1)) = 1 := by
      rw [pow_mul]; norm_num
    have e2 : ((-1 : ℚ)) ^ (1 + 2 * (m + 1)) = -1 := by
      rw [pow_add, e1]; norm_num
    rw [e1, e2]
    push_cast
    ring
  · have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    simp only [a, h1, h2, if_true, a320047_U0]
    have e1 : ((-1 : ℚ)) ^ (2 * k + 1) = -1 := by
      rw [pow_succ, pow_mul]; norm_num
    have e2 : ((-1 : ℚ)) ^ (1 + (2 * k + 1)) = 1 := by
      rw [pow_add, e1]; norm_num
    rw [e1, e2]
    push_cast
    ring

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a320047.main := by
  refine ⟨fun n hn => a320047_closed n hn, fun n hn => ?_⟩
  rw [a320047_closed n (by omega), a320047_closed (n - 2) (by omega),
    a320047_closed (n - 4) (by omega), a320047_closed (n - 6) (by omega),
    a320047_closed (n - 8) (by omega)]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  have e2 : k + 8 - 2 = k + 6 := by omega
  have e4 : k + 8 - 4 = k + 4 := by omega
  have e6 : k + 8 - 6 = k + 2 := by omega
  have e8 : k + 8 - 8 = k := by omega
  rw [e2, e4, e6, e8]
  unfold a320047F
  push_cast
  ring
