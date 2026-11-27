import OMAStatements.S_oeis_a208658
import Mathlib

namespace A208658aux

open OMA.S_oeis_a208658 in
lemma closed (n : ℕ) (hn : 1 ≤ n) :
    a n = (n : ℤ) * ((2 : ℤ) ^ n - 1) - (2 : ℤ) ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold a
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have s1 : ∑ k ∈ Finset.range (m + 1), ((m + 1).choose (k + 1) : ℤ) = (2 : ℤ) ^ (m + 1) - 1 := by
    have h := Nat.sum_range_choose (m + 1)
    rw [Finset.sum_range_succ', Nat.choose_zero_right] at h
    have h' : ((∑ k ∈ Finset.range (m + 1), (m + 1).choose (k + 1) + 1 : ℕ) : ℤ)
        = ((2 ^ (m + 1) : ℕ) : ℤ) := by rw [h]
    push_cast at h'
    linarith
  have s2 : ∑ k ∈ Finset.range (m + 1), ((m + 1 - 1).choose k : ℤ) = (2 : ℤ) ^ m := by
    rw [Nat.add_sub_cancel]
    exact_mod_cast Nat.sum_range_choose m
  rw [s1, s2, Nat.add_sub_cancel]

open OMA.S_oeis_a208658 in
lemma closedN (n : ℕ) (hn : 1 ≤ n) :
    2 * a n = 2 * (n : ℤ) * ((2 : ℤ) ^ n - 1) - (2 : ℤ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [closed (m + 1) (by omega), Nat.add_sub_cancel]
  ring

open OMA.S_oeis_a208658 in
lemma a0 : a 0 = 0 := by simp [a]
open OMA.S_oeis_a208658 in
lemma a1 : a 1 = 0 := by rw [closed 1 (by norm_num)]; norm_num
open OMA.S_oeis_a208658 in
lemma a2 : a 2 = 4 := by rw [closed 2 (by norm_num)]; norm_num
open OMA.S_oeis_a208658 in
lemma a3 : a 3 = 17 := by rw [closed 3 (by norm_num)]; norm_num
open OMA.S_oeis_a208658 in
lemma a4 : a 4 = 52 := by rw [closed 4 (by norm_num)]; norm_num

open OMA.S_oeis_a208658 in
lemma tail (m : ℕ) :
    a (m + 5) - 6 * a (m + 4) + 13 * a (m + 3) - 12 * a (m + 2) + 4 * a (m + 1) = 0 := by
  have c5 := closedN (m + 5) (by omega)
  have c4 := closedN (m + 4) (by omega)
  have c3 := closedN (m + 3) (by omega)
  have c2 := closedN (m + 2) (by omega)
  have c1 := closedN (m + 1) (by omega)
  push_cast at c5 c4 c3 c2 c1
  have h : 2 * (a (m + 5) - 6 * a (m + 4) + 13 * a (m + 3) - 12 * a (m + 2) + 4 * a (m + 1))
      = 0 := by
    linear_combination c5 - 6 * c4 + 13 * c3 - 12 * c2 + 4 * c1
  linarith

open OMA.S_oeis_a208658 in
lemma gf : (1 - PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X) ^ 2 * F =
    (4 : PowerSeries ℤ) * PowerSeries.X ^ 2 - 7 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 := by
  have h2 : (PowerSeries.C (2 : ℤ) : PowerSeries ℤ) = 2 := by simp
  have h4 : (PowerSeries.C (4 : ℤ) : PowerSeries ℤ) = 4 := by simp
  have h6 : (PowerSeries.C (6 : ℤ) : PowerSeries ℤ) = 6 := by simp
  have h7 : (PowerSeries.C (7 : ℤ) : PowerSeries ℤ) = 7 := by simp
  have h12 : (PowerSeries.C (12 : ℤ) : PowerSeries ℤ) = 12 := by simp
  have h13 : (PowerSeries.C (13 : ℤ) : PowerSeries ℤ) = 13 := by simp
  have hF : (1 - PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X) ^ 2 * F
      = F - PowerSeries.C (6 : ℤ) * (PowerSeries.X ^ 1 * F)
        + PowerSeries.C (13 : ℤ) * (PowerSeries.X ^ 2 * F)
        - PowerSeries.C (12 : ℤ) * (PowerSeries.X ^ 3 * F)
        + PowerSeries.C (4 : ℤ) * (PowerSeries.X ^ 4 * F) := by
    rw [h4, h6, h12, h13]
    ring
  have hR : (4 : PowerSeries ℤ) * PowerSeries.X ^ 2 - 7 * PowerSeries.X ^ 3
        + 2 * PowerSeries.X ^ 4
      = PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 2 - PowerSeries.C (7 : ℤ) * PowerSeries.X ^ 3
        + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 4 := by
    rw [h2, h4, h7]
  rw [hF, hR]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow, F, PowerSeries.coeff_mk]
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | h
  · simp [a0]
  · simp [a0, a1]
  · simp [a0, a1, a2]
  · simp [a0, a1, a2, a3]
  · simp [a0, a1, a2, a3, a4]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
    have ht := tail m
    linarith

end A208658aux

theorem OMA.solution : type_of% @OMA.S_oeis_a208658.main :=
  ⟨A208658aux.closed, A208658aux.gf⟩
