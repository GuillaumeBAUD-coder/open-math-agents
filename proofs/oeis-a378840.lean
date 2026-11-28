import OMAStatements.S_oeis_a378840

/-!
# A378840: the g.f. of A260332 cubed

The tree equation `B = 1 + X * B ^ 4 + X * B ^ 5` has at most one solution in `ℚ⟦X⟧`
(the difference of two solutions is killed by the unit `1 - X * U`), and
`C = 1 + X * C ^ 4 * (1 + C)` is exactly that equation. Cube cancellation works because
`C ^ 2 + C * D + D ^ 2` has constant coefficient `3`, a unit in `ℚ`.
-/

open PowerSeries

namespace OMA

/-- The tree equation `B = 1 + X * B ^ 4 + X * B ^ 5` has at most one solution. -/
lemma tree_unique {B B' : ℚ⟦X⟧}
    (hB : B = 1 + PowerSeries.X * B ^ 4 + PowerSeries.X * B ^ 5)
    (hB' : B' = 1 + PowerSeries.X * B' ^ 4 + PowerSeries.X * B' ^ 5) : B = B' := by
  set U : ℚ⟦X⟧ := B ^ 3 + B ^ 2 * B' + B * B' ^ 2 + B' ^ 3 +
    (B ^ 4 + B ^ 3 * B' + B ^ 2 * B' ^ 2 + B * B' ^ 3 + B' ^ 4) with hU
  have hBb : B - B' = (PowerSeries.X * B ^ 4 + PowerSeries.X * B ^ 5) -
      (PowerSeries.X * B' ^ 4 + PowerSeries.X * B' ^ 5) := by
    have e : B - B' = (1 + PowerSeries.X * B ^ 4 + PowerSeries.X * B ^ 5) -
        (1 + PowerSeries.X * B' ^ 4 + PowerSeries.X * B' ^ 5) := by
      rw [← hB, ← hB']
    rw [e]
    ring
  have key : B - B' = (B - B') * (PowerSeries.X * U) := by
    calc B - B' = (PowerSeries.X * B ^ 4 + PowerSeries.X * B ^ 5) -
          (PowerSeries.X * B' ^ 4 + PowerSeries.X * B' ^ 5) := hBb
      _ = (B - B') * (PowerSeries.X * U) := by
        rw [hU]
        ring
  have hzero : (B - B') * (1 - PowerSeries.X * U) = 0 := by
    have h : (B - B') * (1 - PowerSeries.X * U) =
        (B - B') - (B - B') * (PowerSeries.X * U) := by ring
    rw [h, ← key, sub_self]
  have hun : IsUnit (1 - PowerSeries.X * U : ℚ⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    rw [show PowerSeries.constantCoeff (1 - PowerSeries.X * U) = 1 by simp]
    exact isUnit_one
  have hsub : B - B' = 0 := by
    obtain ⟨v, hv⟩ := hun.exists_right_inv
    calc B - B' = (B - B') * ((1 - PowerSeries.X * U) * v) := by rw [hv, mul_one]
      _ = ((B - B') * (1 - PowerSeries.X * U)) * v := by ring
      _ = 0 := by rw [hzero, zero_mul]
  exact sub_eq_zero.mp hsub

/-- Cubes cancel in `ℚ⟦X⟧` when the constant coefficients are `1`. -/
lemma cube_cancel {C D : ℚ⟦X⟧} (hc : C ^ 3 = D ^ 3)
    (hC : PowerSeries.coeff 0 C = 1) (hD : PowerSeries.coeff 0 D = 1) : C = D := by
  have hC' : PowerSeries.constantCoeff C = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hC
  have hD' : PowerSeries.constantCoeff D = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hD
  have hfac : C ^ 3 - D ^ 3 = (C - D) * (C ^ 2 + C * D + D ^ 2) := by ring
  have hz : (C - D) * (C ^ 2 + C * D + D ^ 2) = 0 := by rw [← hfac, hc, sub_self]
  have hval : PowerSeries.constantCoeff (C ^ 2 + C * D + D ^ 2) = 3 := by
    simp only [map_add, map_pow, map_mul, hC', hD']
    norm_num
  have hun : IsUnit (C ^ 2 + C * D + D ^ 2 : ℚ⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    rw [hval]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  have hsub : C - D = 0 := by
    obtain ⟨v, hv⟩ := hun.exists_right_inv
    calc C - D = (C - D) * ((C ^ 2 + C * D + D ^ 2) * v) := by rw [hv, mul_one]
      _ = ((C - D) * (C ^ 2 + C * D + D ^ 2)) * v := by ring
      _ = 0 := by rw [hz, zero_mul]
  exact sub_eq_zero.mp hsub

end OMA

theorem OMA.solution : type_of% @OMA.S_oeis_a378840.main := by
  intro A C B h1 h2 h3 h4
  have hc : C ^ 3 = (1 + PowerSeries.X * C ^ 4 * (1 + C)) ^ 3 := by rw [← h1, h3]
  have hCD : C = 1 + PowerSeries.X * C ^ 4 * (1 + C) :=
    OMA.cube_cancel hc h2 (by simp)
  have hCtree : C = 1 + PowerSeries.X * C ^ 4 + PowerSeries.X * C ^ 5 := by
    have h := hCD
    rw [show PowerSeries.X * C ^ 4 * (1 + C) =
      PowerSeries.X * C ^ 4 + PowerSeries.X * C ^ 5 from by ring] at h
    simpa [add_assoc] using h
  have hCB : C = B := OMA.tree_unique hCtree h4
  rw [h1, hCB]
