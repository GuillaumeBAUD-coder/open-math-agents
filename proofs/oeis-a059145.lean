import OMAStatements.S_oeis_a059145
import Mathlib

namespace OMA.S_oeis_a059145
open PowerSeries

theorem split2 (f : ℕ → ℕ) (N : ℕ) :
    ∑ j ∈ Finset.range (2 * N), f j = ∑ i ∈ Finset.range N, (f (2 * i) + f (2 * i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ _ N]
    ring

theorem cnt (M : ℕ) : ∑ i ∈ Finset.range (M + 1), (if i = 0 then 0 else 1) = M := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, ih]; simp

theorem T_eq (m : ℕ) :
    ∑ j ∈ Finset.range (2 ^ m), padicValNat 2 j + m + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_comm, split2]
    have h : ∀ i, padicValNat 2 (2 * i) + padicValNat 2 (2 * i + 1) = padicValNat 2 i + (if i = 0 then 0 else 1) := by
      intro i
      have h1 : padicValNat 2 (2 * i + 1) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd; omega
      rw [h1]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp
      · rw [padicValNat.mul (by norm_num) hi.ne']
        simp [hi.ne']
        omega
    simp only [h, Finset.sum_add_distrib]
    have hp : 2 ^ m = (2 ^ m - 1) + 1 := by have := Nat.one_le_two_pow (n := m); omega
    have hc := cnt (2 ^ m - 1)
    rw [← hp] at hc
    omega

theorem a_eq (n : ℕ) : (a n : ℤ) = 3 * (-11 + 2 ^ (4 + n) - 3 * n) := by
  have hT := T_eq (n + 1)
  have hN : 2 ^ (n + 1) = (2 ^ (n + 1) - 1) + 1 := by have := Nat.one_le_two_pow (n := n + 1); omega
  have hs : ∑ k ∈ Finset.range (2 ^ (n + 1) - 1), padicValNat 2 (k + 1)
      = ∑ j ∈ Finset.range (2 ^ (n + 1)), padicValNat 2 j := by
    conv_rhs => rw [hN, Finset.sum_range_succ']
    simp
  have hc : ∀ k, collapsed2 k = 9 * padicValNat 2 k + 15 := by
    intro k; simp [collapsed2, element, ruler]; ring
  have ha : a n = 9 * ∑ k ∈ Finset.range (2 ^ (n + 1) - 1), padicValNat 2 (k + 1) + 15 * (2 ^ (n + 1) - 1) := by
    simp only [a, hc, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
    ring
  rw [ha, hs]
  have hp : (2 : ℤ) ^ (4 + n) = 8 * 2 ^ (n + 1) := by ring
  have hT' : ((∑ j ∈ Finset.range (2 ^ (n + 1)), padicValNat 2 j : ℕ) : ℤ) + (n + 1) + 1 = 2 ^ (n + 1) := by
    exact_mod_cast hT
  have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  push_cast [Nat.cast_sub h1]
  push_cast at hT'
  rw [hp]
  linarith

theorem rec3 (n : ℕ) (hn : 3 ≤ n) : (a n : ℤ) = 4 * a (n - 1) - 5 * a (n - 2) + 2 * a (n - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, show k + 3 - 3 = k by omega,
    a_eq]
  push_cast
  ring

theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (2 * X - 1)) = 3 * (2 * X - 5) := by
  have hq : ∀ n, (a n : ℚ) = 3 * (-11 + 2 ^ (4 + n) - 3 * n) := by
    intro n; exact_mod_cast a_eq n
  have hP : ((X - 1) ^ 2 * (2 * X - 1) : PowerSeries ℚ)
      = PowerSeries.C 2 * X ^ 3 - PowerSeries.C 5 * X ^ 2 + PowerSeries.C 4 * X - 1 := by
    simp only [map_ofNat]; ring
  have hR : (3 * (2 * X - 5) : PowerSeries ℚ) = PowerSeries.C 6 * X - PowerSeries.C 15 := by
    simp only [map_ofNat]; ring
  rw [hP, hR]
  ext m
  simp only [mul_sub, mul_add, map_sub, map_add, mul_one]
  have e : ∀ (c : ℚ) (d : ℕ), PowerSeries.mk (fun n => (a n : ℚ)) * (PowerSeries.C c * X ^ d)
      = PowerSeries.C c * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ d) := by
    intro c d; ring
  have e1 : PowerSeries.mk (fun n => (a n : ℚ)) * (PowerSeries.C 4 * X)
      = PowerSeries.C 4 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1) := by ring
  rw [e, e, e1]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_C, coeff_X, PowerSeries.coeff_mk]
  rcases m with _ | _ | _ | m
  · simp [hq]; norm_num
  · simp [hq]; norm_num
  · simp [hq]; norm_num
  · simp only [hq]
    simp
    ring_nf

end OMA.S_oeis_a059145

theorem OMA.solution : type_of% @OMA.S_oeis_a059145.main :=
  ⟨OMA.S_oeis_a059145.a_eq, OMA.S_oeis_a059145.rec3, OMA.S_oeis_a059145.gf⟩
