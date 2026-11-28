import OMAStatements.S_oeis_a346074
import Mathlib

open OMA.S_oeis_a346074
open PowerSeries

namespace Pa346074

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

noncomputable def cat : PowerSeries ℚ := map (Nat.castRingHom ℚ) catalanSeries

theorem cat_eq : cat ^ 2 * X + 1 = cat := by
  have := congrArg (map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
  simpa [cat] using this

theorem catalan_subst (u : PowerSeries ℚ) (hu : constantCoeff u = 0) :
    (catalanSeries.map (Nat.castRingHom ℚ)).subst u ^ 2 * u + 1 =
      (catalanSeries.map (Nat.castRingHom ℚ)).subst u := by
  have ha := HasSubst.of_constantCoeff_zero' hu
  have hc := congrArg (substAlgHom ha) cat_eq
  rw [map_add, map_mul, map_pow, map_one, substAlgHom_X, coe_substAlgHom] at hc
  exact hc

noncomputable def A : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)

theorem hA (i : ℕ) : coeff i A = (a i : ℚ) := by rw [A, coeff_mk]

theorem T_coeff (j : ℕ) : coeff j (A - X ^ 5 * A ^ 2) = 1 := by
  rcases j with _ | _ | _ | _ | _ | m
  all_goals rw [map_sub, coeff_X_pow_mul', hA]
  · simp [a]
  · simp [a]
  · simp [a]
  · simp [a]
  · simp [a]
  · rw [if_pos (by omega), show m + 1 + 1 + 1 + 1 + 1 - 5 = m by omega, pow_two, coeff_mul]
    simp only [hA]
    rw [show m + 1 + 1 + 1 + 1 + 1 = m + 5 by omega, a]
    push_cast
    rw [Fin.sum_univ_eq_sum_range (fun k => (a k : ℚ) * a (m - k)),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    ring

theorem two_step : (1 - X) * (A - X ^ 5 * A ^ 2) = 1 := by
  have hT := T_coeff
  generalize (A - X ^ 5 * A ^ 2) = T at hT ⊢
  ext m
  rw [sub_mul, one_mul]
  rcases m with _ | m
  · simpa using hT 0
  · rw [map_sub, coeff_succ_X_mul, hT, hT, coeff_one]
    simp

theorem quad : (X ^ 5 - X ^ 6) * A ^ 2 + (-1 + X) * A + (1) = 0 := by
  linear_combination (-1 : PowerSeries ℚ) * two_step

theorem ode : (X - 2 * X ^ 2 + X ^ 3 - 4 * X ^ 6 + 4 * X ^ 7) * d⁄dX ℚ A + (5 - 10 * X + 5 * X ^ 2 - 10 * X ^ 5 + 12 * X ^ 6) * A = 5 - 4 * X := by
  set S : PowerSeries ℚ := 2 * (X ^ 5 - X ^ 6) * A + (-1 + X) with hSdef
  have hS : S ^ 2 = (-1 + X) ^ 2 - 4 * (X ^ 5 - X ^ 6) * (1) := by
    rw [hSdef]; linear_combination (4 * (X ^ 5 - X ^ 6)) * quad
  have hA : 2 * (X ^ 5 - X ^ 6) * A = -(-1 + X) + S := by rw [hSdef]; ring
  have hdD : d⁄dX ℚ ((-1 + X) ^ 2 - 4 * (X ^ 5 - X ^ 6) * (1)) = -2 + 2 * X - 20 * X ^ 4 + 24 * X ^ 5 := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have hda : d⁄dX ℚ (2 * (X ^ 5 - X ^ 6)) = 10 * X ^ 4 - 12 * X ^ 5 := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have hdb : d⁄dX ℚ (-1 + X) = 1 := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have h1 : 2 * S * d⁄dX ℚ S = -2 + 2 * X - 20 * X ^ 4 + 24 * X ^ 5 := by
    have := congrArg (d⁄dX ℚ) hS
    rw [derivative_pow, hdD] at this
    rw [← this]; push_cast; ring
  have E1 : (10 * X ^ 4 - 12 * X ^ 5) * A + 2 * (X ^ 5 - X ^ 6) * d⁄dX ℚ A = -(1) + d⁄dX ℚ S := by
    have := congrArg (d⁄dX ℚ) hA
    rw [Derivation.leibniz, map_add, map_neg, hda, hdb, smul_eq_mul, smul_eq_mul] at this
    linear_combination this
  have E2 : 2 * ((-1 + X) ^ 2 - 4 * (X ^ 5 - X ^ 6) * (1)) * d⁄dX ℚ S = (-2 + 2 * X - 20 * X ^ 4 + 24 * X ^ 5) * S := by
    linear_combination (-2 * d⁄dX ℚ S) * hS + S * h1
  have key : (2 * ((-1 + X) ^ 2 - 4 * (X ^ 5 - X ^ 6) * (1)) * (2 * (X ^ 5 - X ^ 6))) *
      ((X - 2 * X ^ 2 + X ^ 3 - 4 * X ^ 6 + 4 * X ^ 7) * d⁄dX ℚ A + (5 - 10 * X + 5 * X ^ 2 - 10 * X ^ 5 + 12 * X ^ 6) * A - (5 - 4 * X)) = 0 := by
    linear_combination (2 * ((-1 + X) ^ 2 - 4 * (X ^ 5 - X ^ 6) * (1)) * (X - 2 * X ^ 2 + X ^ 3 - 4 * X ^ 6 + 4 * X ^ 7)) * E1 +
      (X - 2 * X ^ 2 + X ^ 3 - 4 * X ^ 6 + 4 * X ^ 7) * E2 - ((X - 2 * X ^ 2 + X ^ 3 - 4 * X ^ 6 + 4 * X ^ 7) * (-2 + 2 * X - 20 * X ^ 4 + 24 * X ^ 5)) * hA
  have hne : ((2 : PowerSeries ℚ) * ((-1 + X) ^ 2 - 4 * (X ^ 5 - X ^ 6) * (1)) * (2 * (X ^ 5 - X ^ 6))) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne ?_) (mul_ne_zero two_ne ?_)
    · intro h0
      have := congrArg constantCoeff h0
      simp only [map_ofNat, map_mul, map_sub, map_add, map_neg, map_pow, constantCoeff_X,
        constantCoeff_one, map_one] at this
      norm_num at this
    · rw [show (X ^ 5 - X ^ 6 : PowerSeries ℚ) = X ^ 5 * (1 - X) by ring]
      refine mul_ne_zero (pow_ne_zero _ X_ne_zero) ?_
      intro h0
      have := congrArg constantCoeff h0
      simp at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

end Pa346074

theorem OMA.solution : type_of% @OMA.S_oeis_a346074.main := by
  intro n hn
  have e := congrArg (coeff n) Pa346074.ode
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  simp only [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega, show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega, show k + 6 - 5 = k + 1 by omega, show k + 6 - 6 = k by omega]
  simp only [Pa346074.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa346074.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X,
    coeff_one] at e
  simp at e
  simp only [Pa346074.A, coeff_mk, add_assoc, Nat.reduceAdd] at e
  qify
  push_cast at e ⊢
  linarith
