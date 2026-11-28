import OMAStatements.S_oeis_a281946
import Mathlib

open OMA.S_oeis_a281946

namespace P281946

open Finset

def g (k : ℕ) : ℚ := (k.choose 3 : ℚ) + 3 * (k.choose 4 : ℚ)

lemma toRangeA (n : ℕ) : ∑ k ∈ Icc 3 (n + 2), ((k.choose 3 : ℚ) + 3 * (k.choose 4 : ℚ)) / ((n + 2 - k).factorial : ℚ) =
    ∑ k ∈ range (n + 3), g k / ((n + 2 - k).factorial : ℚ) := by
  apply Finset.sum_subset
  · intro k hk; simp only [mem_Icc] at hk; simp only [mem_range]; omega
  · intro k hk hk'
    simp only [mem_Icc, mem_range] at hk hk'
    rw [Nat.choose_eq_zero_of_lt (by omega : k < 3), Nat.choose_eq_zero_of_lt (by omega : k < 4)]; simp

lemma toRangeB (n : ℕ) : ∑ k ∈ Icc 2 (n + 1), (k.choose 2 : ℚ) / ((n + 1 - k).factorial : ℚ) =
    ∑ k ∈ range (n + 2), (k.choose 2 : ℚ) / ((n + 1 - k).factorial : ℚ) := by
  apply Finset.sum_subset
  · intro k hk; simp only [mem_Icc] at hk; simp only [mem_range]; omega
  · intro k hk hk'
    simp only [mem_Icc, mem_range] at hk hk'
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

def T (n : ℕ) : ℚ := ∑ i ∈ range (n + 2), ((n + 1 - i).choose 2 : ℚ) / (i.factorial : ℚ)

def U (n : ℕ) : ℚ := ∑ i ∈ range (n + 3), g (n + 2 - i) / (i.factorial : ℚ)

lemma bT (n : ℕ) : b n = (n.factorial : ℚ) * T n := by
  unfold b T
  rw [toRangeB, ← Finset.sum_range_reflect]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi; simp only [mem_range] at hi
  rw [show n + 2 - 1 - i = n + 1 - i by omega, show n + 1 - (n + 1 - i) = i by omega]

lemma aU (n : ℕ) : a n = (n.factorial : ℚ) * U n := by
  unfold a U
  rw [toRangeA, ← Finset.sum_range_reflect]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi; simp only [mem_range] at hi
  rw [show n + 3 - 1 - i = n + 2 - i by omega, show n + 2 - (n + 2 - i) = i by omega]

lemma c3 (K : ℕ) : 3 * (K.choose 3 : ℚ) = ((K : ℚ) - 2) * (K.choose 2 : ℚ) := by
  rcases Nat.lt_or_ge K 2 with h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]; simp
  · have e := Nat.choose_succ_right_eq K 2
    have e' : (K.choose 3 : ℚ) * 3 = (K.choose 2 : ℚ) * ((K - 2 : ℕ) : ℚ) := by exact_mod_cast e
    rw [Nat.cast_sub h] at e'; push_cast at e'
    linear_combination e'

lemma gstep (K : ℕ) : g (K + 1) = g K + ((K : ℚ) - 1) * (K.choose 2 : ℚ) := by
  unfold g
  rw [Nat.choose_succ_succ' K 2, Nat.choose_succ_succ' K 3]
  push_cast
  linear_combination c3 K

lemma sumi (m : ℕ) : ∑ i ∈ range (m + 3), (i : ℚ) * ((m + 2 - i).choose 2 : ℚ) / (i.factorial : ℚ) = T m := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
  unfold T
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.factorial_succ, show m + 2 - (i + 1) = m + 1 - i by omega]; push_cast
  have : ((i : ℚ) + 1) ≠ 0 := by positivity
  have : (i.factorial : ℚ) ≠ 0 := by positivity
  field_simp

lemma Ustep (m : ℕ) : U (m + 1) = U m + ((m : ℚ) + 1) * T (m + 1) - T m := by
  unfold U
  rw [Finset.sum_range_succ, show m + 1 + 2 - (m + 3) = 0 by omega]
  simp only [g, Nat.choose_zero_succ, Nat.cast_zero, mul_zero, add_zero, zero_div]
  rw [← sumi m]
  unfold T
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi; simp only [mem_range] at hi
  rw [show m + 1 + 2 - i = (m + 2 - i) + 1 by omega, show m + 1 + 1 - i = m + 2 - i by omega]
  have hg := gstep (m + 2 - i)
  unfold g at hg
  rw [hg, Nat.cast_sub (by omega)]
  push_cast
  have : (i.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

lemma stir2 (j : ℕ) : Nat.stirlingSecond (2 + j) j = (j + 2).choose 3 + 3 * (j + 2).choose 4 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2 + (j + 1) = (2 + j) + 1 by omega, Nat.stirlingSecond_succ_succ, ih,
      show 2 + j = j + 1 + 1 by omega, Nat.stirlingSecond_succ_self_left]
    rw [show j + 1 + 2 = (j + 2) + 1 by omega, Nat.choose_succ_succ' (j + 2) 2, Nat.choose_succ_succ' (j + 2) 3,
      show j + 1 + 1 = j + 2 by omega]
    have e := Nat.choose_succ_right_eq (j + 2) 2
    rw [show j + 2 - 2 = j by omega] at e
    nlinarith [e]

end P281946

open P281946 in
theorem OMA.solution : type_of% @OMA.S_oeis_a281946.main := by
  constructor
  · intro n hn
    rw [aU]
    unfold A U
    have hs : ∀ j, (Nat.stirlingSecond (2 + j) j : ℚ) = g (j + 2) := by
      intro j; rw [stir2, g]; push_cast; ring
    simp only [hs]
    rw [Finset.sum_range_reflect (fun i => g (n + 2 - i) / (i.factorial : ℚ)) (n + 3) |>.symm]
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [show n + 3 - 1 - 0 = n + 2 by omega, show n + 3 - 1 - (0 + 1) = n + 1 by omega,
      show n + 2 - (n + 2) = 0 by omega, show n + 2 - (n + 1) = 1 by omega]
    rw [show g 1 = 0 by unfold g; simp [Nat.choose], show g 0 = 0 by unfold g; simp]
    simp only [zero_div, add_zero]
    simp only [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj; simp only [Finset.mem_range] at hj
    rw [show n + 3 - 1 - (j + 1 + 1) = n - j by omega, show n + 2 - (n - j) = j + 2 by omega,
      add_comm 2 n, Nat.factorial_succ (n + 1), Nat.factorial_succ n, show Nat.factorial (2 + 1) = 6 from rfl]
    rw [Nat.cast_choose_two]
    push_cast
    have : ((n - j).factorial : ℚ) ≠ 0 := by positivity
    have : (n : ℚ) + 1 ≠ 0 := by positivity
    have : (n : ℚ) + 2 ≠ 0 := by positivity
    have : (n : ℚ) + 2 - 1 ≠ 0 := by
      have : (0 : ℚ) ≤ n := by positivity
      intro h; linarith
    field_simp
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show m + 1 - 1 = m by omega, aU, aU, bT, bT, Ustep, Nat.factorial_succ]
    push_cast
    ring
