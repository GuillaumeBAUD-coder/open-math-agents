import OMAStatements.S_oeis_a317023
import Mathlib

open Finset OMA.S_oeis_a317023 in
theorem OMA.solution : type_of% @OMA.S_oeis_a317023.main := by
  have h : ∀ m, target (m + 1) = ∑ p ∈ antidiagonal m, (-1 : ℤ) ^ p.1 * (p.1.choose p.2) := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero => simp [target]
    | one => simp [target, Nat.antidiagonal_succ]
    | more n h1 h2 =>
      rw [target, h1, h2, Nat.antidiagonal_succ_succ', Nat.antidiagonal_succ']
      simp [Nat.choose_succ_succ, sum_add_distrib, pow_succ, mul_add]
      ring
  intro n
  rcases n with _ | n
  · simp [entry, target]
  · rw [h, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [entry, mul_sub, sum_sub_distrib]
    rw [Int.alternating_sum_range_choose_of_ne n.succ_ne_zero, sum_range_succ']
    simp [pow_succ]
