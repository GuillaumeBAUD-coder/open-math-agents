import OMAStatements.S_oeis_a187430
import Mathlib

namespace OMA.Helpers

open PowerSeries

/-- The cofactor in `Φ(S) - Φ(u) = (S - u) * K` for `Φ(Z) = Z (1 - Z^2)^2 - q (1 + Z^3)^2`. -/
noncomputable def a187430Cof (S u q : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  -S^5*q - S^4*q*u + S^4 - S^3*q*u^2 + S^3*u - S^2*q*u^3 - 2*S^2*q + S^2*u^2 - 2*S^2
    - S*q*u^4 - 2*S*q*u + S*u^3 - 2*S*u - q*u^5 - 2*q*u^2 + u^4 - 2*u^2 + 1

theorem a187430_unique (S u q : ℚ⟦X⟧) (hS0 : constantCoeff S = 0) (hu0 : constantCoeff u = 0)
    (hq0 : constantCoeff q = 0)
    (hS : S * (1 - S ^ 2) ^ 2 = q * (1 + S ^ 3) ^ 2)
    (hu : u * (1 - u ^ 2) ^ 2 = q * (1 + u ^ 3) ^ 2) : S = u := by
  have hprod : (S - u) * a187430Cof S u q = 0 := by
    unfold a187430Cof
    linear_combination hS - hu
  have hK : a187430Cof S u q ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp [a187430Cof, hS0, hu0, hq0] at this
  have := (mul_eq_zero.mp hprod).resolve_right hK
  exact sub_eq_zero.mp this

end OMA.Helpers

open OMA.Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a187430.main := by
  intro F C hF0 hF hC
  have hX1 : constantCoeff (1 - X : ℚ⟦X⟧) ≠ 0 := by simp
  have hinv : ((1 - X : ℚ⟦X⟧)⁻¹) * (1 - X) = 1 := PowerSeries.inv_mul_cancel _ hX1
  set q : ℚ⟦X⟧ := -(X * ((1 - X : ℚ⟦X⟧)⁻¹) ^ 2) with hqdef
  have hq0 : constantCoeff q = 0 := by simp [hqdef]
  have hq : q * (1 - X) ^ 2 = -X := by
    rw [hqdef]
    linear_combination (-(X : ℚ⟦X⟧) * ((1 - X : ℚ⟦X⟧)⁻¹ * (1 - X) + 1)) * hinv
  have ha : HasSubst q := HasSubst.of_constantCoeff_zero' hq0
  have hS : (PowerSeries.subst q F : ℚ⟦X⟧) * (1 - (PowerSeries.subst q F : ℚ⟦X⟧) ^ 2) ^ 2
      = q * (1 + (PowerSeries.subst q F : ℚ⟦X⟧) ^ 3) ^ 2 := by
    have h1 := congrArg (substAlgHom ha) hF
    simp only [map_mul, map_sub, map_pow, map_add, map_one, substAlgHom_X, coe_substAlgHom] at h1
    exact h1
  have hS0 : constantCoeff (PowerSeries.subst q F : ℚ⟦X⟧) = 0 := by
    have hF0' : constantCoeff F = 0 := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hF0
    exact constantCoeff_subst_eq_zero hq0 F hF0'
  have hC0 : constantCoeff C = 1 := by
    have := congrArg constantCoeff hC
    simpa using this
  have hu0 : constantCoeff (1 - C) = 0 := by simp [hC0]
  have hu : (1 - C) * (1 - (1 - C) ^ 2) ^ 2 = q * (1 + (1 - C) ^ 3) ^ 2 := by
    have hne : ((1 - X : ℚ⟦X⟧) ^ 2) ≠ 0 := by
      apply pow_ne_zero
      intro h
      apply hX1
      rw [h]
      simp
    have h2 : ((1 - C) * (1 - (1 - C) ^ 2) ^ 2 - q * (1 + (1 - C) ^ 3) ^ 2) * (1 - X) ^ 2 = 0 := by
      linear_combination (-C^4 + C^3*X + 4*C^3 - 5*C^2*X - 4*C^2 + 8*C*X - 4*X) * hC
        - (1 + (1 - C) ^ 3) ^ 2 * hq
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hne)
  have := a187430_unique _ _ q hS0 hu0 hq0 hS hu
  rw [this]
  ring
