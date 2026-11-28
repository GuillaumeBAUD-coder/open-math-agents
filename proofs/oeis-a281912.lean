import OMAStatements.S_oeis_a281912
import Mathlib

open OMA.S_oeis_a281912

namespace P281912

open Finset

lemma toRange (n : ℕ) : ∑ k ∈ Icc 2 (n + 1), (k.choose 2 : ℚ) / ((n + 1 - k).factorial : ℚ) =
    ∑ k ∈ range (n + 2), (k.choose 2 : ℚ) / ((n + 1 - k).factorial : ℚ) := by
  apply Finset.sum_subset
  · intro k hk; simp only [mem_Icc] at hk; simp only [mem_range]; omega
  · intro k hk hk'
    simp only [mem_Icc, mem_range] at hk hk'
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

def T (n : ℕ) : ℚ := ∑ i ∈ range (n + 2), ((n + 1 - i).choose 2 : ℚ) / (i.factorial : ℚ)

def S (n : ℕ) : ℚ := ∑ i ∈ range (n + 1), 1 / (i.factorial : ℚ)

lemma aT (n : ℕ) : a n = (n.factorial : ℚ) * T n := by
  unfold a T
  rw [toRange, ← Finset.sum_range_reflect]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi; simp only [mem_range] at hi
  rw [show n + 2 - 1 - i = n + 1 - i by omega, show n + 1 - (n + 1 - i) = i by omega]

lemma eS (n : ℕ) : e n = (n.factorial : ℚ) * S n := by
  unfold e S; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

lemma sumi (m : ℕ) : ∑ i ∈ range (m + 2), (i : ℚ) / (i.factorial : ℚ) = S m := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_div, add_zero]
  unfold S
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.factorial_succ]; push_cast
  have : ((i : ℚ) + 1) ≠ 0 := by positivity
  have : (i.factorial : ℚ) ≠ 0 := by positivity
  field_simp

lemma Tstep (m : ℕ) : T (m + 1) = T m + ((m : ℚ) + 1) * S (m + 1) - S m := by
  unfold T
  rw [Finset.sum_range_succ, show m + 1 + 1 - (m + 2) = 0 by omega]
  simp only [Nat.choose_zero_succ, Nat.cast_zero, zero_div, add_zero]
  rw [← sumi m]
  unfold S
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi; simp only [mem_range] at hi
  rw [show m + 1 + 1 - i = (m + 1 - i) + 1 by omega, Nat.choose_succ_succ', Nat.choose_one_right]
  push_cast
  rw [Nat.cast_sub (by omega)]; push_cast
  have : (i.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

lemma stir (j : ℕ) : (Nat.stirlingSecond (1 + j) j : ℚ) = ((j + 1).choose 2 : ℚ) := by
  rw [add_comm, Nat.stirlingSecond_succ_self_left]

end P281912

open P281912 in
theorem OMA.solution : type_of% @OMA.S_oeis_a281912.main := by
  constructor
  · intro n hn
    rw [aT]
    unfold A T
    simp only [stir]
    rw [Finset.sum_range_reflect (fun i => ((n + 1 - i).choose 2 : ℚ) / (i.factorial : ℚ)) (n + 2) |>.symm]
    rw [Finset.sum_range_succ']
    simp only [show n + 2 - 1 - 0 = n + 1 by omega, Nat.sub_self, Nat.choose_zero_succ, Nat.cast_zero,
      zero_div, add_zero]
    simp only [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj; simp only [Finset.mem_range] at hj
    rw [show n + 2 - 1 - (j + 1) = n - j by omega, show n + 1 - (n - j) = j + 1 by omega,
      add_comm 1 n, Nat.factorial_succ n, show Nat.factorial (1 + 1) = 2 from rfl]
    push_cast
    have : ((n - j).factorial : ℚ) ≠ 0 := by positivity
    have : (n : ℚ) + 1 ≠ 0 := by positivity
    field_simp
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show m + 1 - 1 = m by omega, aT, aT, eS, eS, Tstep, Nat.factorial_succ]
    push_cast
    ring
