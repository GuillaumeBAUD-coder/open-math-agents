import OMAStatements.S_oeis_a177126
import Mathlib

/-!
The coefficient-extraction argument follows @caa1982's submission for the adjacent
sequence A177125 (open-math-agents PR 22203). Here the second initial term
is ten. This changes the quadratic equation of the generating series, its
discriminant, and the differential equation whose coefficients are extracted.
-/

open OMA.S_oeis_a177126
open PowerSeries

namespace Pa177126

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * d⁄dX ℚ F) = coeff k F * k := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem two_ne : (2 : PowerSeries ℚ) ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  rw [map_ofNat, map_zero] at this
  norm_num at this

noncomputable def A : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)

/-- Removing the shifted convolution leaves the inhomogeneous term for each index. -/
theorem T_coeff (j : ℕ) :
    coeff j (A - 1 - 10 * X - X * (A ^ 2 - 1)) = if j < 2 then 0 else (j : ℚ) * 1 + 1 := by
  have hA : ∀ i, coeff i A = (a i : ℚ) := fun i => by rw [A, coeff_mk]
  have hCX : ∀ i, coeff i (10 * X : PowerSeries ℚ) = if i = 1 then (10 : ℚ) else 0 := by
    intro i
    rw [show (10 * X : PowerSeries ℚ) = C (10 : ℚ) * X by simp [nC], coeff_C_mul, coeff_X]
    split_ifs <;> simp
  rcases j with _ | _ | n
  · rw [map_sub, map_sub, map_sub, coeff_zero_X_mul, hA, hCX, coeff_one]
    simp [a]
  · rw [map_sub, map_sub, map_sub, coeff_succ_X_mul, hA, hCX, coeff_one, map_sub, coeff_one,
      pow_two, coeff_mul]
    simp [hA, a]
  · rw [map_sub, map_sub, map_sub, coeff_succ_X_mul, map_sub, coeff_one, if_neg (by omega),
      coeff_one, if_neg (by omega), hA, hCX, if_neg (by omega), pow_two, coeff_mul]
    simp only [hA]
    rw [if_neg (by omega), a]
    push_cast
    rw [Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range (fun p => (a p : ℚ) * a (n + 1 - p)),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp
    ring

theorem two_step : (1 - X) ^ 2 * (A - 1 - 10 * X - X * (A ^ 2 - 1)) =
    1 * X * (2 * X - X ^ 2) + 1 * X ^ 2 * (1 - X) := by
  have hT := T_coeff
  generalize (A - 1 - 10 * X - X * (A ^ 2 - 1)) = T at hT ⊢
  ext m
  have e : (1 - X) ^ 2 * T = T - 2 * (X * T) + X * (X * T) := by ring
  rw [e]
  rcases m with _ | _ | _ | _ | m
  all_goals simp only [map_add, map_sub, nC, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul,
    hT, pow_succ, pow_zero, one_mul, mul_assoc, coeff_X, coeff_one, map_neg, neg_mul]
  all_goals norm_num
  all_goals push_cast
  all_goals ring

theorem quad : (X * (1 - X) ^ 2) * A ^ 2 + (-(1 - X) ^ 2) * A + (1 + 7 * X - 14 * X ^ 2 + 7 * X ^ 3) = 0 := by
  linear_combination (-1 : PowerSeries ℚ) * two_step

/-- Eliminate the square of the series to obtain a first-order differential equation. -/
theorem ode : (X - 7 * X ^ 2 - 21 * X ^ 3 + 83 * X ^ 4 - 84 * X ^ 5 + 28 * X ^ 6) * d⁄dX ℚ A + (1 - 5 * X + 9 * X ^ 2 - X ^ 3) * A = 1 + 15 * X - 42 * X ^ 2 + 42 * X ^ 3 - 14 * X ^ 4 := by
  set S : PowerSeries ℚ := 2 * (X * (1 - X) ^ 2) * A + (-(1 - X) ^ 2) with hSdef
  have hS : S ^ 2 = (-(1 - X) ^ 2) ^ 2 - 4 * (X * (1 - X) ^ 2) * (1 + 7 * X - 14 * X ^ 2 + 7 * X ^ 3) := by
    rw [hSdef]; linear_combination (4 * (X * (1 - X) ^ 2)) * quad
  have hA : 2 * (X * (1 - X) ^ 2) * A = -(-(1 - X) ^ 2) + S := by rw [hSdef]; ring
  have hdD : d⁄dX ℚ ((-(1 - X) ^ 2) ^ 2 - 4 * (X * (1 - X) ^ 2) * (1 + 7 * X - 14 * X ^ 2 + 7 * X ^ 3)) = -8 - 28 * X + 312 * X ^ 2 - 668 * X ^ 3 + 560 * X ^ 4 - 168 * X ^ 5 := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    simp only [map_ofNat]
    push_cast
    ring
  have hda : d⁄dX ℚ (2 * (X * (1 - X) ^ 2)) = 2 - 8 * X + 6 * X ^ 2 := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    simp only [map_ofNat]
    push_cast
    ring
  have hdb : d⁄dX ℚ (-(1 - X) ^ 2) = 2 - 2 * X := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    simp only [map_ofNat]
    push_cast
    ring
  have h1 : 2 * S * d⁄dX ℚ S = -8 - 28 * X + 312 * X ^ 2 - 668 * X ^ 3 + 560 * X ^ 4 - 168 * X ^ 5 := by
    have := congrArg (d⁄dX ℚ) hS
    rw [derivative_pow, hdD] at this
    rw [← this]; push_cast; ring
  have E1 : (2 - 8 * X + 6 * X ^ 2) * A + 2 * (X * (1 - X) ^ 2) * d⁄dX ℚ A = -(2 - 2 * X) + d⁄dX ℚ S := by
    have := congrArg (d⁄dX ℚ) hA
    rw [Derivation.leibniz, map_add, map_neg, hda, hdb, smul_eq_mul, smul_eq_mul] at this
    linear_combination this
  have E2 : 2 * ((-(1 - X) ^ 2) ^ 2 - 4 * (X * (1 - X) ^ 2) * (1 + 7 * X - 14 * X ^ 2 + 7 * X ^ 3)) * d⁄dX ℚ S = (-8 - 28 * X + 312 * X ^ 2 - 668 * X ^ 3 + 560 * X ^ 4 - 168 * X ^ 5) * S := by
    linear_combination (-2 * d⁄dX ℚ S) * hS + S * h1
  have key : (2 * ((-(1 - X) ^ 2) ^ 2 - 4 * (X * (1 - X) ^ 2) * (1 + 7 * X - 14 * X ^ 2 + 7 * X ^ 3)) * (2 * (X * (1 - X) ^ 2))) *
      ((X - 7 * X ^ 2 - 21 * X ^ 3 + 83 * X ^ 4 - 84 * X ^ 5 + 28 * X ^ 6) * d⁄dX ℚ A + (1 - 5 * X + 9 * X ^ 2 - X ^ 3) * A - (1 + 15 * X - 42 * X ^ 2 + 42 * X ^ 3 - 14 * X ^ 4)) = 0 := by
    linear_combination (2 * ((-(1 - X) ^ 2) ^ 2 - 4 * (X * (1 - X) ^ 2) * (1 + 7 * X - 14 * X ^ 2 + 7 * X ^ 3)) * (X - 7 * X ^ 2 - 21 * X ^ 3 + 83 * X ^ 4 - 84 * X ^ 5 + 28 * X ^ 6)) * E1 +
      (X - 7 * X ^ 2 - 21 * X ^ 3 + 83 * X ^ 4 - 84 * X ^ 5 + 28 * X ^ 6) * E2 - ((X - 7 * X ^ 2 - 21 * X ^ 3 + 83 * X ^ 4 - 84 * X ^ 5 + 28 * X ^ 6) * (-8 - 28 * X + 312 * X ^ 2 - 668 * X ^ 3 + 560 * X ^ 4 - 168 * X ^ 5)) * hA
  have hne : ((2 : PowerSeries ℚ) * ((-(1 - X) ^ 2) ^ 2 - 4 * (X * (1 - X) ^ 2) * (1 + 7 * X - 14 * X ^ 2 + 7 * X ^ 3)) * (2 * (X * (1 - X) ^ 2))) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne ?_) (mul_ne_zero two_ne ?_)
    · intro h0
      have := congrArg constantCoeff h0
      simp only [map_ofNat, map_mul, map_sub, map_add, map_neg, map_pow, constantCoeff_X,
        constantCoeff_one, map_one] at this
      norm_num at this
    · refine mul_ne_zero X_ne_zero ?_
      intro h0
      have := congrArg constantCoeff h0
      simp only [map_ofNat, map_mul, map_sub, map_add, map_neg, map_pow, constantCoeff_X,
        constantCoeff_one, map_one] at this
      norm_num at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

end Pa177126

theorem OMA.solution : type_of% @OMA.S_oeis_a177126.main := by
  intro n hn
  have e := congrArg (coeff n) Pa177126.ode
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega, show k + 5 - 5 = k by omega]
  simp only [Pa177126.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa177126.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X,
    coeff_one] at e
  simp at e
  simp only [Pa177126.A, coeff_mk] at e
  qify
  push_cast at e ⊢
  linear_combination ((k : ℚ) + 5) * e
