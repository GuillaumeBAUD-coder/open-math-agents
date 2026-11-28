import OMAStatements.S_oeis_a378840
import Mathlib

namespace OMA.P_oeis_a378840

private theorem main_proved :
    ∀ (A C B : PowerSeries ℚ),
      A = C ^ 3 →
      PowerSeries.coeff 0 C = 1 →
      A = (1 + PowerSeries.X * C ^ 4 * (1 + C)) ^ 3 →
      B = 1 + PowerSeries.X * B ^ 4 + PowerSeries.X * B ^ 5 →
      A = B ^ 3 := by
  intro A C B hAC hC0 hAeq hB
  -- Step 1: C^3 = D^3 with D = 1 + X * C^4 * (1 + C), so (C - D) * (C^2 + C*D + D^2) = 0.
  -- Since coeff 0 (C^2 + C*D + D^2) = 3 ≠ 0 in ℚ, C^2 + C*D + D^2 is a unit, hence C = D!
  set D : PowerSeries ℚ := 1 + PowerSeries.X * C ^ 4 * (1 + C)
  have hCD3 : C ^ 3 = D ^ 3 := hAC.symm.trans hAeq
  have hprod : (C - D) * (C ^ 2 + C * D + D ^ 2) = 0 := by
    linear_combination hCD3
  have hD0 : PowerSeries.constantCoeff D = 1 := by
    simp [D]
  have hC0' : PowerSeries.constantCoeff C = 1 := by
    rwa [← PowerSeries.coeff_zero_eq_constantCoeff]
  have hU_unit : IsUnit (C ^ 2 + C * D + D ^ 2) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have hval : PowerSeries.constantCoeff (C ^ 2 + C * D + D ^ 2) = (3 : ℚ) := by
      simp [hC0', hD0]
      norm_num
    rw [hval]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  have hCeqD : C = D := by
    obtain ⟨u, hu⟩ := hU_unit
    have hmul : (C - D) * (u : PowerSeries ℚ) = 0 := by rwa [hu]
    have hsub : C - D = 0 := by
      have := congr_arg (· * (↑u⁻¹ : PowerSeries ℚ)) hmul
      simp only [mul_assoc, Units.mul_inv, mul_one, zero_mul] at this
      exact this
    exact sub_eq_zero.mp hsub
  have hC_rec : C = 1 + PowerSeries.X * C ^ 4 + PowerSeries.X * C ^ 5 := by
    calc C = 1 + PowerSeries.X * C ^ 4 * (1 + C) := hCeqD
      _ = 1 + PowerSeries.X * C ^ 4 + PowerSeries.X * C ^ 5 := by ring
  -- Step 2: Uniqueness of solutions to F = 1 + X * F^4 + X * F^5 by strong induction on n!
  have hCB : C = B := by
    ext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hpow_agree : ∀ (r m : ℕ), m < n →
          PowerSeries.coeff m (C ^ r) = PowerSeries.coeff m (B ^ r) := by
        intro r
        induction r with
        | zero => intro m _; simp
        | succ r ihr =>
          intro m hm
          rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (f := fun i j => PowerSeries.coeff i (C ^ r) * PowerSeries.coeff j C),
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (f := fun i j => PowerSeries.coeff i (B ^ r) * PowerSeries.coeff j B)]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          rw [ihr k (by omega), ih (m - k) (by omega)]
      cases n with
      | zero =>
        rw [hC_rec, hB]
        simp [PowerSeries.coeff_zero_eq_constantCoeff]
      | succ m =>
        rw [hC_rec, hB]
        simp only [map_add, PowerSeries.coeff_succ_X_mul]
        rw [hpow_agree 4 m (Nat.lt_succ_self m), hpow_agree 5 m (Nat.lt_succ_self m)]
  rw [hAC, hCB]

end OMA.P_oeis_a378840

theorem OMA.solution : type_of% @OMA.S_oeis_a378840.main :=
  OMA.P_oeis_a378840.main_proved
