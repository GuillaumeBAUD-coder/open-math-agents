import OMAStatements.S_oeis_a002376
import Mathlib.Tactic

namespace OMA.P_oeis_a002376

open OMA.S_oeis_a002376

private lemma coeff_X_pow_mul_eq (f : PowerSeries ℤ) (m n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.X : PowerSeries ℤ) ^ m * f) =
      if m ≤ n then PowerSeries.coeff (n - m) f else 0 := by
  rw [PowerSeries.coeff_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single (m, n - m)]
    · simp [PowerSeries.coeff_X_pow]
    · rintro ⟨a, b⟩ hab hne
      rw [Finset.mem_antidiagonal] at hab
      have ham : a ≠ m := fun ha => hne (Prod.ext ha (by omega))
      dsimp only
      rw [PowerSeries.coeff_X_pow, if_neg ham, zero_mul]
    · intro hnot
      exact absurd (Finset.mem_antidiagonal.mpr (by omega)) hnot
  · refine Finset.sum_eq_zero fun ⟨a, b⟩ hab => ?_
    rw [Finset.mem_antidiagonal] at hab
    have ham : a ≠ m := by omega
    dsimp only
    rw [PowerSeries.coeff_X_pow, if_neg ham, zero_mul]

private lemma A002376_27_le_one : A002376 27 ≤ 1 := by
  unfold A002376
  refine Nat.sInf_le ?_
  exact ⟨fun _ => 3, fun _ => by norm_num, by norm_num⟩

private theorem prove_disproof : ¬ type_of% @OMA.S_oeis_a002376.main := by
  intro hEq
  set A : PowerSeries ℤ := PowerSeries.mk fun k => (A002376 (k + 1) : ℤ)
  have hId : (1 - (PowerSeries.X : PowerSeries ℤ) - PowerSeries.X ^ 8 + PowerSeries.X ^ 9) * A =
      1 + PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 + PowerSeries.X ^ 4 +
        PowerSeries.X ^ 5 + PowerSeries.X ^ 6 - PowerSeries.C (6 : ℤ) * PowerSeries.X ^ 7 := by
    have hL : ((PowerSeries.X : PowerSeries ℤ) + 1) * (PowerSeries.X ^ 2 + 1) *
        (PowerSeries.X ^ 4 + 1) * (PowerSeries.X - 1) ^ 2 =
        1 - PowerSeries.X - PowerSeries.X ^ 8 + PowerSeries.X ^ 9 := by ring
    have hR : -(-1 - (PowerSeries.X : PowerSeries ℤ) - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 -
        PowerSeries.X ^ 4 - PowerSeries.X ^ 5 - PowerSeries.X ^ 6 +
        PowerSeries.C (6 : ℤ) * PowerSeries.X ^ 7) =
        1 + PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 + PowerSeries.X ^ 4 +
        PowerSeries.X ^ 5 + PowerSeries.X ^ 6 - PowerSeries.C (6 : ℤ) * PowerSeries.X ^ 7 := by ring
    rw [← hL, ← hR]
    exact hEq
  have hstep : ∀ n : ℕ,
      (A002376 (n + 1) : ℤ) -
        (if 1 ≤ n then (A002376 n : ℤ) else 0) -
        (if 8 ≤ n then (A002376 (n - 7) : ℤ) else 0) +
        (if 9 ≤ n then (A002376 (n - 8) : ℤ) else 0) =
      (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0) + (if n = 2 then 1 else 0) +
        (if n = 3 then 1 else 0) + (if n = 4 then 1 else 0) + (if n = 5 then 1 else 0) +
        (if n = 6 then 1 else 0) - 6 * (if n = 7 then 1 else 0) := by
    intro n
    have hc := congrArg (PowerSeries.coeff n) hId
    rw [add_mul, sub_mul, sub_mul, one_mul,
      map_add, map_sub, map_sub,
      map_sub, map_add, map_add, map_add, map_add, map_add, map_add,
      PowerSeries.coeff_C_mul] at hc
    rw [show (PowerSeries.X : PowerSeries ℤ) * A = PowerSeries.X ^ 1 * A by rw [pow_one]] at hc
    rw [coeff_X_pow_mul_eq, coeff_X_pow_mul_eq, coeff_X_pow_mul_eq,
      PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow] at hc
    simp only [A, PowerSeries.coeff_mk] at hc
    have h1 : (if 1 ≤ n then (A002376 (n - 1 + 1) : ℤ) else 0) =
        (if 1 ≤ n then (A002376 n : ℤ) else 0) := by
      split_ifs with h
      · rw [Nat.sub_add_cancel h]
      · rfl
    have h8 : (if 8 ≤ n then (A002376 (n - 8 + 1) : ℤ) else 0) =
        (if 8 ≤ n then (A002376 (n - 7) : ℤ) else 0) := by
      split_ifs with h
      · rw [show n - 8 + 1 = n - 7 by omega]
      · rfl
    have h9 : (if 9 ≤ n then (A002376 (n - 9 + 1) : ℤ) else 0) =
        (if 9 ≤ n then (A002376 (n - 8) : ℤ) else 0) := by
      split_ifs with h
      · rw [show n - 9 + 1 = n - 8 by omega]
      · rfl
    rw [h1, h8, h9] at hc
    exact hc
  have hrec : ∀ n : ℕ, 9 ≤ n →
      (A002376 (n + 1) : ℤ) =
        (A002376 n : ℤ) + (A002376 (n - 7) : ℤ) - (A002376 (n - 8) : ℤ) := by
    intro n hn
    have h := hstep n
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h
    linarith
  have h1 : (A002376 1 : ℤ) = 1 := by
    have h := hstep 0
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h
    norm_num at h; linarith
  have h2 : (A002376 2 : ℤ) = 2 := by
    have h := hstep 1
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)] at h
    norm_num [h1] at h; linarith
  have h3 : (A002376 3 : ℤ) = 3 := by
    have h := hstep 2
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)] at h
    norm_num [h2] at h; linarith
  have h4 : (A002376 4 : ℤ) = 4 := by
    have h := hstep 3
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)] at h
    norm_num [h3] at h; linarith
  have h5 : (A002376 5 : ℤ) = 5 := by
    have h := hstep 4
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)] at h
    norm_num [h4] at h; linarith
  have h6 : (A002376 6 : ℤ) = 6 := by
    have h := hstep 5
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)] at h
    norm_num [h5] at h; linarith
  have h7 : (A002376 7 : ℤ) = 7 := by
    have h := hstep 6
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)] at h
    norm_num [h6] at h; linarith
  have h8 : (A002376 8 : ℤ) = 1 := by
    have h := hstep 7
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)] at h
    norm_num [h7] at h; linarith
  have h9 : (A002376 9 : ℤ) = 2 := by
    have h := hstep 8
    rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h
    norm_num [h1, h8] at h; linarith
  have h10 : (A002376 10 : ℤ) = 3 := by have h := hrec 9 (by omega); norm_num [h1, h2, h9] at h; linarith
  have h11 : (A002376 11 : ℤ) = 4 := by have h := hrec 10 (by omega); norm_num [h2, h3, h10] at h; linarith
  have h12 : (A002376 12 : ℤ) = 5 := by have h := hrec 11 (by omega); norm_num [h3, h4, h11] at h; linarith
  have h13 : (A002376 13 : ℤ) = 6 := by have h := hrec 12 (by omega); norm_num [h4, h5, h12] at h; linarith
  have h14 : (A002376 14 : ℤ) = 7 := by have h := hrec 13 (by omega); norm_num [h5, h6, h13] at h; linarith
  have h15 : (A002376 15 : ℤ) = 8 := by have h := hrec 14 (by omega); norm_num [h6, h7, h14] at h; linarith
  have h16 : (A002376 16 : ℤ) = 2 := by have h := hrec 15 (by omega); norm_num [h7, h8, h15] at h; linarith
  have h17 : (A002376 17 : ℤ) = 3 := by have h := hrec 16 (by omega); norm_num [h8, h9, h16] at h; linarith
  have h18 : (A002376 18 : ℤ) = 4 := by have h := hrec 17 (by omega); norm_num [h9, h10, h17] at h; linarith
  have h19 : (A002376 19 : ℤ) = 5 := by have h := hrec 18 (by omega); norm_num [h10, h11, h18] at h; linarith
  have h20 : (A002376 20 : ℤ) = 6 := by have h := hrec 19 (by omega); norm_num [h11, h12, h19] at h; linarith
  have h21 : (A002376 21 : ℤ) = 7 := by have h := hrec 20 (by omega); norm_num [h12, h13, h20] at h; linarith
  have h22 : (A002376 22 : ℤ) = 8 := by have h := hrec 21 (by omega); norm_num [h13, h14, h21] at h; linarith
  have h23 : (A002376 23 : ℤ) = 9 := by have h := hrec 22 (by omega); norm_num [h14, h15, h22] at h; linarith
  have h24 : (A002376 24 : ℤ) = 3 := by have h := hrec 23 (by omega); norm_num [h15, h16, h23] at h; linarith
  have h25 : (A002376 25 : ℤ) = 4 := by have h := hrec 24 (by omega); norm_num [h16, h17, h24] at h; linarith
  have h26 : (A002376 26 : ℤ) = 5 := by have h := hrec 25 (by omega); norm_num [h17, h18, h25] at h; linarith
  have h27 : (A002376 27 : ℤ) = 6 := by have h := hrec 26 (by omega); norm_num [h18, h19, h26] at h; linarith
  have hle : (A002376 27 : ℤ) ≤ 1 := by exact_mod_cast A002376_27_le_one
  linarith

end OMA.P_oeis_a002376

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a002376.main) :=
  OMA.P_oeis_a002376.prove_disproof
