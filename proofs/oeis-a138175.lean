import OMAStatements.S_oeis_a138175
import Mathlib

open OMA.S_oeis_a138175
open PowerSeries

namespace P138175

theorem exT : ∃ T : ℚ⟦X⟧, T - T ^ 3 = X ∧ coeff 0 T = 0 := by
  let f : Polynomial ℚ⟦X⟧ := Polynomial.X ^ 3 - Polynomial.X + Polynomial.C X
  have hm : f.Monic := by
    unfold f
    rw [sub_add]
    exact (Polynomial.monic_X_pow 3).sub_of_left (by
      rw [Polynomial.degree_X_pow]
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) ?_
      rw [Polynomial.degree_X]
      exact max_lt (by norm_num) (lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)))
  have h0 : f.eval 0 ∈ (Ideal.span {X} : Ideal ℚ⟦X⟧) := by
    simp only [f, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C]
    simpa using Ideal.subset_span (Set.mem_singleton (X : ℚ⟦X⟧))
  have h1 : IsUnit (Ideal.Quotient.mk (Ideal.span {X} : Ideal ℚ⟦X⟧) (f.derivative.eval 0)) := by
    have : f.derivative.eval 0 = -1 := by
      simp [f]
    rw [this, map_neg, map_one]
    exact (isUnit_one (M := ℚ⟦X⟧ ⧸ (Ideal.span {X} : Ideal ℚ⟦X⟧))).neg
  obtain ⟨a, ha, ha0⟩ := HenselianRing.is_henselian f hm 0 h0 h1
  refine ⟨a, ?_, ?_⟩
  · have := ha.eq_zero
    simp only [f, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at this
    linear_combination -this
  · rw [sub_zero, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at ha0
    rw [coeff_zero_eq_constantCoeff_apply]; exact ha0

end P138175

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a138175.main) := by
  intro h
  obtain ⟨T, hT, hT0⟩ := P138175.exT
  have hc : constantCoeff (1 - 2 * T) ≠ 0 := by
    have : constantCoeff T = 0 := by rwa [← coeff_zero_eq_constantCoeff_apply]
    simp [this, map_ofNat]
  let G : ℚ⟦X⟧ := (1 - 2 * T)⁻¹
  have hG : G * (1 - 2 * T) = 1 := PowerSeries.inv_mul_cancel _ hc
  have e := h T G hT hT0 hG 3 le_rfl
  obtain ⟨U, rfl⟩ : X ∣ T := by
    rw [PowerSeries.X_dvd_iff, ← coeff_zero_eq_constantCoeff_apply]; exact hT0
  have hU : U - X ^ 2 * U ^ 3 = 1 := by
    have : X * (U - X ^ 2 * U ^ 3 - 1) = 0 := by linear_combination hT
    linear_combination (mul_eq_zero.mp this).resolve_left PowerSeries.X_ne_zero
  have hG' : G - X * (C (2 : ℚ) * (U * G)) = 1 := by rw [← map_ofNat C 2] at hG; linear_combination hG
  have u0 := congrArg (coeff 0) hU
  have u1 := congrArg (coeff 1) hU
  have u2 := congrArg (coeff 2) hU
  have g0 := congrArg (coeff 0) hG'
  have g1 := congrArg (coeff 1) hG'
  have g2 := congrArg (coeff 2) hG'
  have g3 := congrArg (coeff 3) hG'
  simp only [map_sub, coeff_one, map_mul, mul_assoc, coeff_X_pow_mul', coeff_C_mul,
    coeff_succ_X_mul, coeff_zero_X_mul] at u0 u1 u2 g0 g1 g2 g3
  norm_num at u0 u1 u2 g0 g1 g2 g3
  simp only [coeff_mul, Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_cons,
    Finset.sum_singleton, Finset.map_cons, Finset.map_singleton] at u2 g1 g2 g3
  simp at u2 g1 g2 g3
  norm_num at e
  rw [u0] at u2 g1 g2 g3
  rw [g0] at g1 g2 g3 e
  rw [u1] at g2 g3
  have hu2 : coeff 2 U = 1 := by linarith
  rw [hu2] at g3
  have hg1 : coeff 1 G = 2 := by linarith
  rw [hg1] at g2 g3 e
  have hg2 : coeff 2 G = 4 := by linarith
  rw [hg2] at g3 e
  have hg3 : coeff 3 G = 10 := by linarith
  rw [hg3] at e
  norm_num at e
