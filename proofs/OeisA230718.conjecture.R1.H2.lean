import OMAReductions.R_OeisA230718_conjecture_R1
import Mathlib

-- Step OeisA230718.conjecture.R1.H2: hypothesis H2 of reduction OeisA230718.conjecture.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Write `N = M + 1`, `A = N ^ n`, `B = M ^ n`, `P = ∑ i < M, i ^ n`. The ratios `(i - 1) ^ n / i ^ n`
increase with `i`, so termwise `A * i ^ n ≤ B * (i + 1) ^ n` for `i < M`, giving `A * P ≤ B * (P + B)`.
Bernoulli's inequality gives `(x + 1) ^ n * x ≥ x ^ n * (x + n)` and
`(x - 1) ^ n * (x + 1) ^ n * x ^ 2 ≥ x ^ (2n) * (x ^ 2 - n)` for `x = M`. If `3 B ≥ 2 A`, the first
forces `x ≥ 2 n`, while the pair condition `B + (x - 1) ^ n ≤ A` with the second forces
`x ^ 2 ≤ 4 n`, a contradiction. So `3 B < 2 A`, and then `A * P ≤ B * (P + B)` yields
`P + B < 2 A`. -/

namespace P4A230718

open Finset

theorem ratio_term (M n i : ℕ) (hi : i + 1 ≤ M) :
    (M + 1) ^ n * i ^ n ≤ M ^ n * (i + 1) ^ n := by
  rw [← mul_pow, ← mul_pow]
  apply Nat.pow_le_pow_left
  have e1 : (M + 1) * i = M * i + i := by ring
  have e2 : M * (i + 1) = M * i + M := by ring
  omega

theorem sum_ratio (M n : ℕ) (hn : 0 < n) :
    (M + 1) ^ n * (∑ i ∈ range M, i ^ n) ≤ M ^ n * ∑ i ∈ range (M + 1), i ^ n := by
  have h1 : ∑ i ∈ range (M + 1), i ^ n = ∑ i ∈ range M, (i + 1) ^ n := by
    rw [Finset.sum_range_succ', zero_pow hn.ne', add_zero]
  rw [h1, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact ratio_term M n i (by simp at hi; omega)

theorem bern1 (x : ℝ) (n : ℕ) (hx : 0 < x) :
    x ^ n * (x + n) ≤ (x + 1) ^ n * x := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / x by
    have : 0 < 1 / x := by positivity
    linarith) n
  have e : (x + 1) ^ n = x ^ n * (1 + 1 / x) ^ n := by
    rw [← mul_pow]; congr 1; field_simp
  rw [e]
  have h2 : x ^ n * (1 + n * (1 / x)) ≤ x ^ n * (1 + 1 / x) ^ n :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have e2 : x ^ n * (1 + n * (1 / x)) * x = x ^ n * (x + n) := by field_simp
  nlinarith

theorem bern2 (x : ℝ) (n : ℕ) (hx : 1 ≤ x) :
    (x ^ n) ^ 2 * (x ^ 2 - n) ≤ (x - 1) ^ n * (x + 1) ^ n * x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(1 / x ^ 2) by
    have : 1 / x ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith) n
  have e : (x - 1) ^ n * (x + 1) ^ n = (x ^ n) ^ 2 * (1 + -(1 / x ^ 2)) ^ n := by
    rw [← mul_pow, ← pow_mul, mul_comm n 2, pow_mul, ← mul_pow]
    congr 1
    field_simp
    ring
  rw [e]
  have h2 : (x ^ n) ^ 2 * (1 + n * -(1 / x ^ 2)) ≤ (x ^ n) ^ 2 * (1 + -(1 / x ^ 2)) ^ n :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have e2 : (x ^ n) ^ 2 * (1 + n * -(1 / x ^ 2)) * x ^ 2 = (x ^ n) ^ 2 * (x ^ 2 - n) := by
    field_simp; ring
  nlinarith [sq_nonneg x]

theorem key_ineq (x : ℝ) (n : ℕ) (hx : 2 ≤ x) (hn : 2 ≤ n)
    (hpair : x ^ n + (x - 1) ^ n ≤ (x + 1) ^ n) : 3 * x ^ n < 2 * (x + 1) ^ n := by
  by_contra hcon
  have hcon := not_lt.mp hcon
  have hx0 : 0 < x := by linarith
  have hB : 0 < x ^ n := by positivity
  have hC : 0 ≤ (x - 1) ^ n := by
    have : 0 ≤ x - 1 := by linarith
    positivity
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have b1 := bern1 x n hx0
  have b2 := bern2 x n (by linarith)
  set A := (x + 1) ^ n with hA
  set B := x ^ n with hB'
  set C := (x - 1) ^ n with hC'
  -- 2n ≤ x
  have h1 : 2 * (n : ℝ) ≤ x := by
    have h : B * (2 * n) ≤ B * x := by nlinarith
    exact le_of_mul_le_mul_left h hB
  -- x^2 ≤ 4n
  have hAB : B ≤ A := by linarith
  have h2 : (A - B) * A ≤ 3 / 4 * B ^ 2 := by nlinarith
  have h3 : C * A * x ^ 2 ≤ (A - B) * A * x ^ 2 := by
    have : C ≤ A - B := by linarith
    have hA0 : 0 ≤ A := by linarith
    have := mul_le_mul_of_nonneg_right this hA0
    nlinarith [sq_nonneg x]
  have h4 : B ^ 2 * (x ^ 2 - n) ≤ 3 / 4 * B ^ 2 * x ^ 2 := by nlinarith [sq_nonneg x]
  have h5 : x ^ 2 - n ≤ 3 / 4 * x ^ 2 := by
    have hB2 : 0 < B ^ 2 := by positivity
    have : B ^ 2 * (x ^ 2 - n) ≤ B ^ 2 * (3 / 4 * x ^ 2) := by linarith
    exact le_of_mul_le_mul_left this hB2
  nlinarith

end P4A230718

open Finset P4A230718 in
theorem OMA.solution : OMA.R_OeisA230718_conjecture_R1.H2 := by
  intro n N hn hN hN3 hpair
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hM2 : 2 ≤ M := by omega
  simp only [Nat.add_sub_cancel] at hpair
  have hpair' : M ^ n + (M - 1) ^ n ≤ (M + 1) ^ n := by
    have : M + 1 - 2 = M - 1 := by omega
    rw [this] at hpair; exact hpair
  have hk : 3 * M ^ n < 2 * (M + 1) ^ n := by
    have hr : ((M : ℝ) ^ n + ((M : ℝ) - 1) ^ n) ≤ ((M : ℝ) + 1) ^ n := by
      have h := (Nat.cast_le (α := ℝ)).mpr hpair'
      push_cast [Nat.cast_sub (show 1 ≤ M by omega)] at h
      exact h
    have := key_ineq (M : ℝ) n (by exact_mod_cast hM2) (by omega) hr
    exact_mod_cast this
  have hr := sum_ratio M n (by omega)
  rw [Finset.sum_range_succ] at hr ⊢
  generalize hP : ∑ i ∈ range M, i ^ n = P at hr ⊢
  generalize hA : (M + 1) ^ n = A at hr hk ⊢
  generalize hB : M ^ n = B at hr hk ⊢
  by_contra hcon
  have hcon := not_lt.mp hcon
  zify at hr hk hcon ⊢
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ P + B - 2 * A by linarith)
    (show (0 : ℤ) ≤ A - B by linarith), Int.natCast_nonneg A]
