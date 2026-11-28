import OMAStatements.S_oeis_a076035
import Mathlib

/-!
# A076035: Mathar's relation a(n) = 4·A076025(n)

With D = 1 − 4xC(x): 1/D = 1 + 4·xC/D, and (1 − 3xC)/D = (D + xC)/D = 1 + xC/D. For n > 0 the
constant term 1 does not contribute, so [xⁿ] 1/D = 4·[xⁿ] (1 − 3xC)/D (this is the
generating-function argument mentioned in the entry).
-/

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a076035.main := by
  intro n hn
  set C' := OMA.S_oeis_a076035.catalanGF
  set D := OMA.S_oeis_a076035.denominator with hDdef
  have hD : constantCoeff D ≠ 0 := by
    rw [hDdef]; unfold OMA.S_oeis_a076035.denominator; simp
  have hinv : D * D⁻¹ = 1 := PowerSeries.mul_inv_cancel D hD
  have h4 : (C 4 : ℚ⟦X⟧) = 4 := map_ofNat C 4
  have e1 : D⁻¹ = 1 + C 4 * (X * C' * D⁻¹) := by
    have hsum : D + 4 * X * C' = 1 := by
      rw [hDdef]; unfold OMA.S_oeis_a076035.denominator; ring
    calc D⁻¹ = (D + 4 * X * C') * D⁻¹ := by rw [hsum, one_mul]
      _ = D * D⁻¹ + C 4 * (X * C' * D⁻¹) := by rw [h4]; ring
      _ = 1 + C 4 * (X * C' * D⁻¹) := by rw [hinv]
  have e2 : (1 - 3 * X * C') * D⁻¹ = 1 + X * C' * D⁻¹ := by
    have hsum : 1 - 3 * X * C' = D + X * C' := by
      rw [hDdef]; unfold OMA.S_oeis_a076035.denominator; ring
    rw [hsum, add_mul, hinv]
  unfold OMA.S_oeis_a076035.a OMA.S_oeis_a076035.b
  rw [← hDdef, e2]
  conv_lhs => rw [e1]
  rw [map_add, map_add, coeff_C_mul, coeff_one, if_neg (by omega)]
  ring
