import OMAStatements.S_oeis_a141771
import Mathlib

open PowerSeries

namespace OMA.Helpers

theorem a141771_two_ne : (2 : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have := congrArg (coeff 0) h
  rw [← map_ofNat C 2] at this
  simp at this

theorem a141771_SdS (S : ℚ⟦X⟧) (hS2 : S ^ 2 = 1 - 4 * X) : S * d⁄dX ℚ S = -2 := by
  have e4 : (4 : ℚ⟦X⟧) = C (4 : ℚ) := (map_ofNat C 4).symm
  have e2 : (2 : ℚ⟦X⟧) = C (2 : ℚ) := (map_ofNat C 2).symm
  have h := congrArg (d⁄dX ℚ) hS2
  rw [pow_two, Derivation.leibniz, e4, map_sub, Derivation.leibniz, derivative_X, derivative_one,
    derivative_C, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h
  have h2 : (2 : ℚ⟦X⟧) * (S * d⁄dX ℚ S) = 2 * (-2) := by
    have : C (4 : ℚ) = C 2 * C 2 := by rw [← map_mul]; norm_num
    rw [this, ← e2] at h
    linear_combination h
  exact mul_left_cancel₀ a141771_two_ne h2

theorem a141771_s_rec (S : ℚ⟦X⟧) (hS2 : S ^ 2 = 1 - 4 * X) (n : ℕ) :
    ((n : ℚ) + 1) * coeff (n + 1) S = (4 * (n : ℚ) - 2) * coeff n S := by
  have hE : d⁄dX ℚ S - X * (C (4:ℚ) * d⁄dX ℚ S) = C (-2 : ℚ) * S := by
    have e4 : (4 : ℚ⟦X⟧) = C (4 : ℚ) := (map_ofNat C 4).symm
    have e2 : C (-2 : ℚ) = -2 := by rw [map_neg, map_ofNat]
    rw [← e4, e2]
    have h := a141771_SdS S hS2
    linear_combination S * h - (d⁄dX ℚ S) * hS2
  have hc := congrArg (coeff n) hE
  cases n with
  | zero =>
    rw [map_sub, coeff_zero_X_mul, coeff_C_mul, coeff_derivative] at hc
    push_cast at hc ⊢
    linarith
  | succ m =>
    rw [map_sub, coeff_succ_X_mul, coeff_C_mul, coeff_C_mul, coeff_derivative, coeff_derivative] at hc
    push_cast at hc ⊢
    linarith

theorem a141771_b_rec (S : ℚ⟦X⟧) (hS2 : S ^ 2 = 1 - 4 * X) (hS0 : coeff 0 S = 1) (n : ℕ) :
    ((n : ℚ) + 1) * coeff (n + 1) S⁻¹ = (4 * (n : ℚ) + 2) * coeff n S⁻¹ := by
  have hc0 : constantCoeff S ≠ 0 := by rw [← coeff_zero_eq_constantCoeff_apply, hS0]; norm_num
  have hSB : S * S⁻¹ = 1 := PowerSeries.mul_inv_cancel S hc0
  have hE : d⁄dX ℚ S⁻¹ - X * (C (4:ℚ) * d⁄dX ℚ S⁻¹) = C (2 : ℚ) * S⁻¹ := by
    have e4 : (4 : ℚ⟦X⟧) = C (4 : ℚ) := (map_ofNat C 4).symm
    have e2 : C (2 : ℚ) = 2 := by rw [map_ofNat]
    rw [← e4, e2, derivative_inv']
    have h := a141771_SdS S hS2
    linear_combination (S⁻¹ ^ 2 * d⁄dX ℚ S) * hS2 - S⁻¹ * h - (S⁻¹ * S * d⁄dX ℚ S) * hSB
  have hc := congrArg (coeff n) hE
  cases n with
  | zero =>
    rw [map_sub, coeff_zero_X_mul, coeff_C_mul, coeff_derivative] at hc
    push_cast at hc ⊢
    linarith
  | succ m =>
    rw [map_sub, coeff_succ_X_mul, coeff_C_mul, coeff_C_mul, coeff_derivative, coeff_derivative] at hc
    push_cast at hc ⊢
    linarith

theorem a141771_sb (S : ℚ⟦X⟧) (hS2 : S ^ 2 = 1 - 4 * X) (hS0 : coeff 0 S = 1) (n : ℕ) :
    (2 * (n : ℚ) - 1) * coeff n S = -coeff n S⁻¹ := by
  have hc0 : constantCoeff S ≠ 0 := by rw [← coeff_zero_eq_constantCoeff_apply, hS0]; norm_num
  induction n with
  | zero =>
    have hB0 : coeff 0 S⁻¹ = 1 := by
      rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_inv, ← coeff_zero_eq_constantCoeff_apply,
        hS0, inv_one]
    rw [hB0, hS0]; norm_num
  | succ m ih =>
    have h1 := a141771_s_rec S hS2 m
    have h2 := a141771_b_rec S hS2 hS0 m
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    apply mul_left_cancel₀ hm
    push_cast
    linear_combination (2 * (m : ℚ) + 1) * h1 + h2 + (4 * (m : ℚ) + 2) * ih

theorem a141771_main_rel (S G : ℚ⟦X⟧) (hS2 : S ^ 2 = 1 - 4 * X) (hS0 : coeff 0 S = 1)
    (hG : 2 * X * S * (1 + S) ^ 3 * G = (1 - S) * S * (1 + S) ^ 3 + 16 * X ^ 4) :
    X * (C (8 : ℚ) * G) = 1 - S + (1 - S) + (1 - S) + (1 - S) + X * (S⁻¹ + C (3 : ℚ) * S - C (4 : ℚ) + C (4 : ℚ) * X) := by
  have hc0 : constantCoeff S ≠ 0 := by rw [← coeff_zero_eq_constantCoeff_apply, hS0]; norm_num
  have hSB : S * S⁻¹ = 1 := PowerSeries.mul_inv_cancel S hc0
  rw [map_ofNat C 8, map_ofNat C 3, map_ofNat C 4]
  have hS : S ≠ 0 := by
    intro h; rw [h] at hS0; simp at hS0
  have h1S : 1 + S ≠ 0 := by
    intro h
    have := congrArg (coeff 0) h
    rw [map_add, hS0] at this; simp at this
  have hK : 2 * X * S * (1 + S) ^ 3 ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero a141771_two_ne X_ne_zero) hS) (pow_ne_zero _ h1S)
  apply mul_left_cancel₀ hK
  linear_combination 8 * X * hG + (-2 * X ^ 2 * (3 * S ^ 3 + 4 * S ^ 2 * X + 5 * S ^ 2 + S - 16 * X ^ 2 - 4 * X - 1)) * hS2 - (2 * X ^ 2 * (S + 1) ^ 3) * hSB

theorem a141771_g (S G : ℚ⟦X⟧) (hS2 : S ^ 2 = 1 - 4 * X) (hS0 : coeff 0 S = 1)
    (hG : 2 * X * S * (1 + S) ^ 3 * G = (1 - S) * S * (1 + S) ^ 3 + 16 * X ^ 4) (n : ℕ) (hn : 2 ≤ n) :
    4 * coeff n G * ((n : ℚ) + 1) * (2 * (n : ℚ) - 1) = coeff n S⁻¹ * ((n : ℚ) ^ 2 + 7 * n - 6) := by
  have h := congrArg (coeff (n + 1)) (a141771_main_rel S G hS2 hS0 hG)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [coeff_succ_X_mul, map_add, map_sub, coeff_C_mul, coeff_one, coeff_X, coeff_C] at h
  simp at h
  have e1 := a141771_sb S hS2 hS0 (k + 2)
  have e2 := a141771_sb S hS2 hS0 (k + 3)
  have e3 := a141771_b_rec S hS2 hS0 (k + 2)
  push_cast at e1 e2 e3 h ⊢
  have ei : k + 2 + 1 = k + 3 := rfl
  rw [ei] at h e3
  have hpos : (2 * ((k : ℚ) + 2) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hpos
  linear_combination (2 * ((k : ℚ) + 2) + 1) * ((k : ℚ) + 2 + 1) * (2 * ((k : ℚ) + 2) - 1) / 2 * h
    - 2 * ((k : ℚ) + 2 + 1) * (2 * ((k : ℚ) + 2) - 1) * e2 + 2 * (2 * ((k : ℚ) + 2) - 1) * e3
    + 3 / 2 * (2 * ((k : ℚ) + 2) + 1) * ((k : ℚ) + 2 + 1) * e1

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a141771.main := by
  intro S G hS2 hS0 hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  have g1 := OMA.Helpers.a141771_g S G hS2 hS0 hG (m + 1) (by omega)
  have g0 := OMA.Helpers.a141771_g S G hS2 hS0 hG m hm
  have br := OMA.Helpers.a141771_b_rec S hS2 hS0 m
  simp only [Nat.add_sub_cancel]
  push_cast at g1 g0 br ⊢
  have hm2 : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hM : 4 * (2 * ((m : ℚ) + 1) - 1) * ((m : ℚ) + 1) * (2 * ((m : ℚ) + 1) - 3) * ((m : ℚ) + 1) ≠ 0 := by
    have a1 : (2 * ((m : ℚ) + 1) - 1) ≠ 0 := by nlinarith
    have a2 : (2 * ((m : ℚ) + 1) - 3) ≠ 0 := by nlinarith
    have a3 : ((m : ℚ) + 1) ≠ 0 := by positivity
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero four_ne_zero a1) a3) a2) a3
  refine (mul_eq_zero.mp ?_).resolve_left hM
  linear_combination ((m : ℚ) + 1) ^ 2 * (2 * ((m : ℚ) + 1) - 3) * (((m : ℚ) + 1) ^ 2 + 5 * ((m : ℚ) + 1) - 12) * (((m : ℚ) + 1) ^ 3 - 5 * ((m : ℚ) + 1) ^ 2 + 38 * ((m : ℚ) + 1) - 250) * g1
    - 2 * (2 * ((m : ℚ) + 1) - 1) * ((m : ℚ) + 1) * (2 * ((m : ℚ) + 1) - 3) * (((m : ℚ) + 1) ^ 2 + 7 * ((m : ℚ) + 1) - 6) * (((m : ℚ) + 1) ^ 3 - 5 * ((m : ℚ) + 1) ^ 2 + 38 * ((m : ℚ) + 1) - 250) * g0
    + ((m : ℚ) + 1) * (2 * ((m : ℚ) + 1) - 3) * (((m : ℚ) + 1) ^ 2 + 5 * ((m : ℚ) + 1) - 12) * (((m : ℚ) + 1) ^ 2 + 7 * ((m : ℚ) + 1) - 6) * (((m : ℚ) + 1) ^ 3 - 5 * ((m : ℚ) + 1) ^ 2 + 38 * ((m : ℚ) + 1) - 250) * br
