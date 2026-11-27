import OMAStatements.S_oeis_a074355
import Mathlib

/-!
Refutation at the coefficient of x^4. Unfolding the recurrence, nu(2) = 4, nu(3) = 7 + 3q and
nu(4) = 19 + 15q + 12q^2, so a(0..4) = 0, 0, 0, 3, 15. Since
(1 - 3x - 3x^2)^2 = 1 - 6x + 3x^2 + 18x^3 + 9x^4, the coefficient of x^4 on the left is
a(4) - 6a(3) + 3a(2) + 18a(1) + 9a(0) = -3, while on the right it is 9.
-/

namespace R074355
open OMA.S_oeis_a074355

theorem nu2 : nu 1 3 2 = Polynomial.C 4 := by
  simp only [nu, Finset.sum_range_succ, Finset.sum_range_zero, map_one, map_ofNat]
  ring

theorem nu3 : nu 1 3 3 = Polynomial.C 7 + Polynomial.C 3 * Polynomial.X := by
  simp only [nu, Finset.sum_range_succ, Finset.sum_range_zero, map_one, map_ofNat]
  ring

theorem nu4 : nu 1 3 4 = Polynomial.C 19 + Polynomial.C 15 * Polynomial.X +
    Polynomial.C 12 * Polynomial.X ^ 2 := by
  simp only [nu, Finset.sum_range_succ, Finset.sum_range_zero, map_one, map_ofNat]
  ring

theorem a0 : a 0 = 0 := by
  unfold a
  rw [show nu 1 3 0 = 1 from rfl, Polynomial.coeff_one]
  norm_num

theorem a1 : a 1 = 0 := by
  unfold a
  rw [show nu 1 3 1 = Polynomial.C 1 from rfl, Polynomial.coeff_C]
  norm_num

theorem a2 : a 2 = 0 := by
  unfold a
  rw [nu2, Polynomial.coeff_C]
  norm_num

theorem a3 : a 3 = 3 := by
  unfold a
  rw [nu3, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
  norm_num

theorem a4 : a 4 = 15 := by
  unfold a
  rw [nu4, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  norm_num

end R074355

open OMA.S_oeis_a074355 R074355 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a074355.main) := by
  intro h
  have h4 : coeff 4 (mk a * (1 - 3 * (X : ℤ⟦X⟧) - 3 * X ^ 2) ^ 2) =
      coeff 4 (9 * X ^ 4 + 3 * X ^ 3 : ℤ⟦X⟧) := by
    rw [h]
  rw [show ((1 - 3 * (X : ℤ⟦X⟧) - 3 * X ^ 2) ^ 2 : ℤ⟦X⟧) =
      1 - C 6 * X ^ 1 + C 3 * X ^ 2 + C 18 * X ^ 3 + C 9 * X ^ 4 by
      simp only [map_ofNat]; ring,
    show ∀ p : ℤ⟦X⟧, p * (1 - C 6 * X ^ 1 + C 3 * X ^ 2 + C 18 * X ^ 3 + C 9 * X ^ 4) =
      p - C 6 * (p * X ^ 1) + C 3 * (p * X ^ 2) + C 18 * (p * X ^ 3) + C 9 * (p * X ^ 4)
      from fun p => by ring,
    show (9 * X ^ 4 + 3 * X ^ 3 : ℤ⟦X⟧) = C 9 * X ^ 4 + C 3 * X ^ 3 by
      simp only [map_ofNat]] at h4
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C,
    coeff_X_pow] at h4
  norm_num [a0, a1, a2, a3, a4] at h4
