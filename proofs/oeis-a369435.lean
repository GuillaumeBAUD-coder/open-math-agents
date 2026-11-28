import OMAStatements.S_oeis_a369435
import Mathlib

namespace OMA.P_oeis_a369435

open PowerSeries

/-- Power series identity: exp/(1+n-n*exp) = 1 + (n+1) * u/(1-n*u) with u = exp - 1. -/
lemma ps_id (n : ℕ) :
    exp ℚ * (1 + (n : PowerSeries ℚ) - (n : PowerSeries ℚ) * exp ℚ)⁻¹ =
      1 + ((n : PowerSeries ℚ) + 1) *
        ((exp ℚ - 1) * (1 + (n : PowerSeries ℚ) - (n : PowerSeries ℚ) * exp ℚ)⁻¹) := by
  have h : (1 + (n : PowerSeries ℚ) - (n : PowerSeries ℚ) * exp ℚ) *
      (1 + (n : PowerSeries ℚ) - (n : PowerSeries ℚ) * exp ℚ)⁻¹ = 1 := by
    apply PowerSeries.mul_inv_cancel
    simp
  linear_combination h

/-- Laurent series identity for the defining expression of A321189. -/
lemma ls_id (n : ℕ) :
    (1 - 1 / ((n : LaurentSeries ℚ) - 1 / ((exp ℚ - 1 : PowerSeries ℚ) : LaurentSeries ℚ))) =
      ((1 + (exp ℚ - 1) * (1 + (n : PowerSeries ℚ) - (n : PowerSeries ℚ) * exp ℚ)⁻¹
        : PowerSeries ℚ) : LaurentSeries ℚ) := by
  have h : (1 + (n : PowerSeries ℚ) - (n : PowerSeries ℚ) * exp ℚ) *
      (1 + (n : PowerSeries ℚ) - (n : PowerSeries ℚ) * exp ℚ)⁻¹ = 1 := by
    apply PowerSeries.mul_inv_cancel
    simp
  set u : PowerSeries ℚ := exp ℚ - 1 with hu
  set E : PowerSeries ℚ := (1 + (n : PowerSeries ℚ) - (n : PowerSeries ℚ) * exp ℚ)⁻¹ with hE
  have hex : exp ℚ = 1 + u := by rw [hu]; ring
  rw [hex] at h
  have hu0 : u ≠ 0 := by
    intro h0
    have := congrArg (PowerSeries.coeff 1) h0
    simp [hu] at this
  have hU : ((u : PowerSeries ℚ) : LaurentSeries ℚ) ≠ 0 := by
    exact (map_ne_zero_iff (HahnSeries.ofPowerSeries ℤ ℚ) HahnSeries.ofPowerSeries_injective).mpr hu0
  have hL : (1 - (n : LaurentSeries ℚ) * (u : LaurentSeries ℚ)) * (E : LaurentSeries ℚ) = 1 := by
    have := congrArg (HahnSeries.ofPowerSeries ℤ ℚ) h
    simp only [map_mul, map_sub, map_add, map_one, map_natCast] at this
    linear_combination this
  have hD : (1 - (n : LaurentSeries ℚ) * (u : LaurentSeries ℚ)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hL
    exact zero_ne_one hL
  have hD' : (n : LaurentSeries ℚ) - 1 / (u : LaurentSeries ℚ) ≠ 0 := by
    intro h0
    apply hD
    have : (n : LaurentSeries ℚ) = 1 / (u : LaurentSeries ℚ) := sub_eq_zero.mp h0
    rw [this]
    field_simp
    ring
  have hEq : (E : LaurentSeries ℚ) = (1 - (n : LaurentSeries ℚ) * (u : LaurentSeries ℚ))⁻¹ :=
    eq_inv_of_mul_eq_one_right hL
  simp only [map_mul, map_sub, map_add, map_one, map_natCast]
  rw [hEq]
  have hD2 : (n : LaurentSeries ℚ) * (u : LaurentSeries ℚ) - 1 ≠ 0 := by
    intro h0
    apply hD
    linear_combination -h0
  field_simp
  ring

end OMA.P_oeis_a369435

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a369435.main := by
  intro n
  unfold OMA.S_oeis_a369435.A OMA.S_oeis_a369435.a
  rw [OMA.P_oeis_a369435.ls_id, OMA.P_oeis_a369435.ps_id, LaurentSeries.coeff_coe_powerSeries]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : PowerSeries.coeff n (1 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_one, if_neg hn.ne']
    have h2 : ((n : PowerSeries ℚ) + 1) = PowerSeries.C ((n : ℚ) + 1) := by simp
    rw [map_add, map_add, h1, h2, PowerSeries.coeff_C_mul]
    ring
