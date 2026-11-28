import OMAStatements.S_oeis_a202020
import Mathlib

/-! A202020: Mathar's recurrence, derived from the differential equation of the g.f. -/

namespace OMA.Helpers

open PowerSeries

theorem a202020_scaled_ode (S G : ℚ⟦X⟧) (h1 : S ^ 2 = 1 - 8 * X + 12 * X ^ 2)
    (h3 : G * (2 * X ^ 4 - 8 * X ^ 3 + 4 * X ^ 2) = 2 * X ^ 2 - 4 * X + 1 - S) :
    4 * X ^ 2 * ((4 - 36 * X + 108 * X ^ 2 - 124 * X ^ 3 + 36 * X ^ 4) * G
      + (2 - 20 * X + 57 * X ^ 2 - 56 * X ^ 3 + 12 * X ^ 4) * (X * d⁄dX ℚ G))
      = 4 * X ^ 2 * (4 - 12 * X + 12 * X ^ 2) := by
  have h2 := congrArg (d⁄dX ℚ) h1
  have h4 := congrArg (d⁄dX ℚ) h3
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_sub,
    derivative_X, derivative_one, smul_eq_mul] at h2 h4
  have e8 : d⁄dX ℚ (8 : ℚ⟦X⟧) = 0 := by
    rw [show (8 : ℚ⟦X⟧) = C (8 : ℚ) from (map_ofNat C 8).symm]; exact derivative_C
  have e12 : d⁄dX ℚ (12 : ℚ⟦X⟧) = 0 := by
    rw [show (12 : ℚ⟦X⟧) = C (12 : ℚ) from (map_ofNat C 12).symm]; exact derivative_C
  have e2 : d⁄dX ℚ (2 : ℚ⟦X⟧) = 0 := by
    rw [show (2 : ℚ⟦X⟧) = C (2 : ℚ) from (map_ofNat C 2).symm]; exact derivative_C
  have e4 : d⁄dX ℚ (4 : ℚ⟦X⟧) = 0 := by
    rw [show (4 : ℚ⟦X⟧) = C (4 : ℚ) from (map_ofNat C 4).symm]; exact derivative_C
  simp only [e8, e12, e2, e4] at h2 h4
  set S' := d⁄dX ℚ S
  set G' := d⁄dX ℚ G
  linear_combination (2 * X * S') * h1 - (X * S) * h2
    - (X * (-8 + 24 * X)) * h3 + (2 * (1 - 8 * X + 12 * X ^ 2) * X) * h4

theorem a202020_theta (G : ℚ⟦X⟧) (k : ℕ) :
    coeff k (X * d⁄dX ℚ G) = (k : ℚ) * coeff k G := by
  cases k with
  | zero => simp
  | succ k => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

end OMA.Helpers

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a202020.main := by
  intro S G h1 _ h3 n hn
  have hX : (4 * X ^ 2 : ℚ⟦X⟧) ≠ 0 :=
    mul_ne_zero (by
      rw [show (4 : ℚ⟦X⟧) = C (4 : ℚ) from (map_ofNat C 4).symm]
      exact (map_ne_zero_iff C (C_injective)).mpr (by norm_num)) (pow_ne_zero _ X_ne_zero)
  have hL := mul_left_cancel₀ hX (OMA.Helpers.a202020_scaled_ode S G h1 h3)
  have hE : C (4 : ℚ) * G + C (-36 : ℚ) * (X ^ 1 * G) + C (108 : ℚ) * (X ^ 2 * G)
      + C (-124 : ℚ) * (X ^ 3 * G) + C (36 : ℚ) * (X ^ 4 * G)
      + C (2 : ℚ) * (X * d⁄dX ℚ G) + C (-20 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ G))
      + C (57 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ G)) + C (-56 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ G))
      + C (12 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ G))
      = C (4 : ℚ) + C (-12 : ℚ) * X + C (12 : ℚ) * X ^ 2 := by
    rw [pow_one]
    simp only [map_neg, map_ofNat]
    rw [← sub_eq_zero] at hL ⊢
    rw [← hL]; ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have hc := congrArg (coeff (m + 4)) hE
  simp only [map_add, coeff_C_mul, coeff_X_pow_mul', OMA.Helpers.a202020_theta, coeff_C,
    coeff_X, coeff_X_pow] at hc
  have e1 : m + 4 - 1 = m + 3 := by omega
  have e2 : m + 4 - 2 = m + 2 := by omega
  have e3 : m + 4 - 3 = m + 1 := by omega
  have e4 : m + 4 - 4 = m := by omega
  have f1 : (1 : ℕ) ≤ m + 4 := by omega
  have f2 : (2 : ℕ) ≤ m + 4 := by omega
  have f3 : (3 : ℕ) ≤ m + 4 := by omega
  have f4 : (4 : ℕ) ≤ m + 4 := by omega
  have g0 : m + 4 ≠ 0 := by omega
  have g1 : m + 4 ≠ 1 := by omega
  have g2 : m + 4 ≠ 2 := by omega
  simp only [e1, e2, e3, e4, f1, f2, f3, f4, g0, g1, g2, if_true, if_false] at hc
  rw [e1, e2, e3, e4]
  push_cast at hc ⊢
  linear_combination hc
