import OMAStatements.S_oeis_a003477
import Mathlib

namespace A003477

open PowerSeries

/-- First coefficients of the inverse of `(1 - 2X)(1 + X^2)(1 - X - 2X^3)`. -/
lemma first_coeffs (S : ℤ⟦X⟧)
    (h : (1 - C 2 * X) * (1 + X ^ 2) * (1 - X - C 2 * X ^ 3) * S = 1) :
    coeff 1 S = 3 ∧ coeff 4 S = 33 := by
  have key : S = 1 + C (3 : ℤ) * (S * X ^ 1) - C (3 : ℤ) * (S * X ^ 2) + C (5 : ℤ) * (S * X ^ 3)
      - C (6 : ℤ) * (S * X ^ 4) + C (2 : ℤ) * (S * X ^ 5) - C (4 : ℤ) * (S * X ^ 6) := by
    have hC2 : (C (2 : ℤ) : ℤ⟦X⟧) = 2 := map_ofNat C 2
    have hC3 : (C (3 : ℤ) : ℤ⟦X⟧) = 3 := map_ofNat C 3
    have hC4 : (C (4 : ℤ) : ℤ⟦X⟧) = 4 := map_ofNat C 4
    have hC5 : (C (5 : ℤ) : ℤ⟦X⟧) = 5 := map_ofNat C 5
    have hC6 : (C (6 : ℤ) : ℤ⟦X⟧) = 6 := map_ofNat C 6
    rw [hC2] at h
    simp only [hC2, hC3, hC4, hC5, hC6]
    linear_combination h
  have c : ∀ n, coeff n S = coeff n (1 + C (3 : ℤ) * (S * X ^ 1) - C (3 : ℤ) * (S * X ^ 2)
      + C (5 : ℤ) * (S * X ^ 3) - C (6 : ℤ) * (S * X ^ 4) + C (2 : ℤ) * (S * X ^ 5)
      - C (4 : ℤ) * (S * X ^ 6)) := fun n => congrArg (coeff n) key
  have c0 : coeff 0 S = 1 := by
    rw [c 0]
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_one]
    norm_num
  have c1 : coeff 1 S = 3 := by
    rw [c 1]
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_one]
    norm_num [c0]
  have c2 : coeff 2 S = 6 := by
    rw [c 2]
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_one]
    norm_num [c0, c1]
  have c3 : coeff 3 S = 14 := by
    rw [c 3]
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_one]
    norm_num [c0, c1, c2]
  have c4 : coeff 4 S = 33 := by
    rw [c 4]
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_one]
    norm_num [c0, c1, c2, c3]
  exact ⟨c1, c4⟩

/-- Fourth coefficient of the inverse of `(1 - 2X)(1 + X^2)(1 - X)`. -/
lemma second_coeff (S : ℤ⟦X⟧)
    (h : (1 - C 2 * X) * (1 + X ^ 2) * (1 - X) * S = 1) :
    coeff 4 S = 25 := by
  have key : S = 1 + C (3 : ℤ) * (S * X ^ 1) - C (3 : ℤ) * (S * X ^ 2) + C (3 : ℤ) * (S * X ^ 3)
      - C (2 : ℤ) * (S * X ^ 4) := by
    have hC2 : (C (2 : ℤ) : ℤ⟦X⟧) = 2 := map_ofNat C 2
    have hC3 : (C (3 : ℤ) : ℤ⟦X⟧) = 3 := map_ofNat C 3
    rw [hC2] at h
    simp only [hC2, hC3]
    linear_combination h
  have c : ∀ n, coeff n S = coeff n (1 + C (3 : ℤ) * (S * X ^ 1) - C (3 : ℤ) * (S * X ^ 2)
      + C (3 : ℤ) * (S * X ^ 3) - C (2 : ℤ) * (S * X ^ 4)) := fun n => congrArg (coeff n) key
  have c0 : coeff 0 S = 1 := by
    rw [c 0]
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_one]
    norm_num
  have c1 : coeff 1 S = 3 := by
    rw [c 1]
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_one]
    norm_num [c0]
  have c2 : coeff 2 S = 6 := by
    rw [c 2]
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_one]
    norm_num [c0, c1]
  have c3 : coeff 3 S = 12 := by
    rw [c 3]
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_one]
    norm_num [c0, c1, c2]
  rw [c 4]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_one]
  norm_num [c0, c1, c2, c3]

lemma mul_inv_one (φ : ℤ⟦X⟧) (h : constantCoeff φ = 1) : φ * invOfUnit φ 1 = 1 :=
  mul_invOfUnit φ 1 (by rw [h, Units.val_one])

end A003477

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a003477.main) := by
  intro h
  have h4 := h 4 (le_refl 4)
  have ha : ∀ n, OMA.S_oeis_a003477.a n = PowerSeries.coeff n (PowerSeries.invOfUnit
      ((1 - PowerSeries.C 2 * PowerSeries.X) * (1 + PowerSeries.X ^ 2) *
        (1 - PowerSeries.X - PowerSeries.C 2 * PowerSeries.X ^ 3)) 1) := fun n => rfl
  have hb : ∀ n, OMA.S_oeis_a003477.b n = PowerSeries.coeff n (PowerSeries.invOfUnit
      ((1 - PowerSeries.C 2 * PowerSeries.X) * (1 + PowerSeries.X ^ 2) *
        (1 - PowerSeries.X)) 1) := fun n => rfl
  have h1 := A003477.first_coeffs _ (A003477.mul_inv_one
    ((1 - PowerSeries.C 2 * PowerSeries.X) * (1 + PowerSeries.X ^ 2) *
        (1 - PowerSeries.X - PowerSeries.C 2 * PowerSeries.X ^ 3)) (by simp))
  have h2 := A003477.second_coeff _ (A003477.mul_inv_one
    ((1 - PowerSeries.C 2 * PowerSeries.X) * (1 + PowerSeries.X ^ 2) *
        (1 - PowerSeries.X)) (by simp))
  have e : (4 : ℕ) - 3 = 1 := rfl
  rw [e, Finset.sum_range_one, ha 4, hb 4, ha (0 + 1), h1.2, h2] at h4
  have h1' := h1.1
  rw [show (0 : ℕ) + 1 = 1 from rfl] at h4
  rw [h1'] at h4
  norm_num at h4
