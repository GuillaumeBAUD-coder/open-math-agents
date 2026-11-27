import OMAStatements.S_mo_479301
import Mathlib

open Polynomial

/- Qiping Zhou gave the exponent-five counterexample on MathOverflow (answer 513542).
Shivam Patel gave an eventual-negativity argument for all exponents at least four
(MathDB 368293). The proof below uses finitely many row indices. -/

/-- Coefficients of `S m n`. -/
lemma OMA.S_coeff (m n j : ℕ) :
    (OMA.S_mo_479301.S m n).coeff j =
      if j ≤ n then (((n + j).choose j : ℝ)) ^ m else 0 := by
  unfold OMA.S_mo_479301.S
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

/-- The coefficient of `q^2` in `S^5_8 S^5_6 - (S^5_7)^2` is `-499140`. -/
lemma OMA.key :
    (OMA.S_mo_479301.S 5 8 * OMA.S_mo_479301.S 5 6 - OMA.S_mo_479301.S 5 7 ^ 2).coeff 2
      = -499140 := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal (2 : ℕ) : Finset (ℕ × ℕ)) =
      {((0 : ℕ), (2 : ℕ)), (1, 1), (2, 0)} := by decide
  rw [Polynomial.coeff_sub, pow_two, Polynomial.coeff_mul, Polynomial.coeff_mul, hanti]
  simp only [OMA.S_coeff]
  norm_num [Nat.choose]

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_479301.main) := by
  intro h
  have h1 := h 5 (by norm_num) 7 (by norm_num) 2
  have h2 := OMA.key
  simp only [show (7 : ℕ) + 1 = 8 from rfl, show (7 : ℕ) - 1 = 6 from rfl] at h1
  rw [h2] at h1
  norm_num at h1

namespace MO479301Sharp

open OMA.S_mo_479301

private lemma necessary (m n : ℕ) (hn : 1 ≤ n) (hn' : 2 ≤ n - 1)
    (h : QLogConvex (S m)) :
    0 ≤ (((n - 1 + 2).choose 2 : ℝ)) ^ m
      + (((n + 1 + 1).choose 1 : ℝ)) ^ m * (((n - 1 + 1).choose 1 : ℝ)) ^ m
      + (((n + 1 + 2).choose 2 : ℝ)) ^ m
      - (2 * (((n + 2).choose 2 : ℝ)) ^ m + (((n + 1).choose 1 : ℝ)) ^ m * (((n + 1).choose 1 : ℝ)) ^ m) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal (2 : ℕ) : Finset (ℕ × ℕ)) =
      {(0, 2), (1, 1), (2, 0)} := by decide
  have H := h n hn 2
  rw [Polynomial.coeff_sub, pow_two, Polynomial.coeff_mul, Polynomial.coeff_mul, hanti] at H
  have hn2 : 2 ≤ n := by omega
  have hn3 : 2 ≤ n + 1 := by omega
  have hn4 : 1 ≤ n - 1 := by omega
  simp [OMA.S_coeff, hn, hn2, hn3, hn4, hn'] at H ⊢
  linarith

private lemma domination (t : ℕ) :
    (6:ℝ)^(11+t) + 2 * 15^(11+t) < 16^(11+t) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    rw [show 11 + (t+1) = (11+t)+1 by omega, pow_succ, pow_succ, pow_succ]
    nlinarith [show (0:ℝ) ≤ 6^(11+t) by positivity, show (0:ℝ) ≤ 16^(11+t) by positivity]

/-- Every exponent at least four fails already at the quadratic coefficient. -/
theorem fails_all (m : ℕ) (hm : 4 ≤ m) : ¬ QLogConvex (S m) := by
  intro h
  by_cases hl : m < 11
  · interval_cases m
    · have H := necessary _ 23 (by decide) (by decide) h
      norm_num [Nat.choose] at H
    · have H := necessary _ 7 (by decide) (by decide) h
      norm_num [Nat.choose] at H
    · have H := necessary _ 5 (by decide) (by decide) h
      norm_num [Nat.choose] at H
    · have H := necessary _ 4 (by decide) (by decide) h
      norm_num [Nat.choose] at H
    · have H := necessary _ 4 (by decide) (by decide) h
      norm_num [Nat.choose] at H
    · have H := necessary _ 4 (by decide) (by decide) h
      norm_num [Nat.choose] at H
    · have H := necessary _ 4 (by decide) (by decide) h
      norm_num [Nat.choose] at H
  · obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le (show 11 ≤ m by omega)
    have H := necessary _ 3 (by decide) (by decide) h
    norm_num [Nat.choose] at H
    rw [show (15:ℝ) = 5*3 by norm_num, mul_pow] at H
    have D := domination t
    rw [show (15:ℝ) = 5*3 by norm_num, mul_pow,
        show (16:ℝ) = 4*4 by norm_num, mul_pow] at D
    nlinarith [show (0:ℝ) ≤ 10^(11+t) by positivity]

end MO479301Sharp
