import OMAStatements.S_oeis_a365847

/-!
# A365847: two characterisations of the same quartic tree series

With `y = X * A` the first hypothesis is `y * (1 - y) ^ 4 = X * (1 + y) ^ 4`, and the second
hypothesis says `X * B ^ 4 = (B - 1) / (B + 1)`. Since `X * B ^ 4` also satisfies the quartic
equation, and that equation has at most one solution in `ℚ⟦X⟧` with zero constant coefficient,
`X * A = X * B ^ 4`, whence `A = B ^ 4`.
-/

open PowerSeries

namespace OMA

/-- The quartic equation `y * (1 - y) ^ 4 = X * (1 + y) ^ 4` has at most one solution with zero
constant coefficient. -/
lemma quartic_unique {a b : ℚ⟦X⟧} (ha0 : PowerSeries.coeff 0 a = 0)
    (hb0 : PowerSeries.coeff 0 b = 0)
    (ha : a * (1 - a) ^ 4 = PowerSeries.X * (1 + a) ^ 4)
    (hb : b * (1 - b) ^ 4 = PowerSeries.X * (1 + b) ^ 4) : a = b := by
  set W : ℚ⟦X⟧ := 1 - 4 * (a + b) + 6 * (a ^ 2 + a * b + b ^ 2) - 4 * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3)
    + (a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4) with hW
  set V : ℚ⟦X⟧ := 4 + 6 * (a + b) + 4 * (a ^ 2 + a * b + b ^ 2) + (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) with hV
  have e1 : a * (1 - a) ^ 4 - b * (1 - b) ^ 4 = (a - b) * W := by
    rw [hW]
    ring
  have e2 : (1 + a) ^ 4 - (1 + b) ^ 4 = (a - b) * V := by
    rw [hV]
    ring
  have key : (a - b) * W = (a - b) * (PowerSeries.X * V) := by
    calc (a - b) * W = a * (1 - a) ^ 4 - b * (1 - b) ^ 4 := e1.symm
      _ = PowerSeries.X * (1 + a) ^ 4 - PowerSeries.X * (1 + b) ^ 4 := by rw [ha, hb]
      _ = PowerSeries.X * ((1 + a) ^ 4 - (1 + b) ^ 4) := by ring
      _ = PowerSeries.X * ((a - b) * V) := by rw [e2]
      _ = (a - b) * (PowerSeries.X * V) := by ring
  have hzero : (a - b) * (W - PowerSeries.X * V) = 0 := by
    have h : (a - b) * (W - PowerSeries.X * V) = (a - b) * W - (a - b) * (PowerSeries.X * V) := by
      ring
    rw [h, key, sub_self]
  have hval : PowerSeries.constantCoeff (W - PowerSeries.X * V) = 1 := by
    have h1 : PowerSeries.constantCoeff a = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact ha0
    have h2 : PowerSeries.constantCoeff b = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hb0
    simp only [hW, hV, map_sub, map_add, map_mul, map_pow, h1, h2]
    norm_num
  have hun : IsUnit (W - PowerSeries.X * V : ℚ⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    rw [hval]
    exact isUnit_one
  have hsub : a - b = 0 := by
    obtain ⟨v, hv⟩ := hun.exists_right_inv
    calc a - b = (a - b) * ((W - PowerSeries.X * V) * v) := by rw [hv, mul_one]
      _ = ((a - b) * (W - PowerSeries.X * V)) * v := by ring
      _ = 0 := by rw [hzero, zero_mul]
  exact sub_eq_zero.mp hsub

end OMA

theorem OMA.solution : type_of% @OMA.S_oeis_a365847.main := by
  intro A B h1 h2
  have hB : B * (1 - PowerSeries.X * B ^ 4) = 1 + PowerSeries.X * B ^ 4 := by
    have h : B * (1 - PowerSeries.X * B ^ 4) - (1 + PowerSeries.X * B ^ 4) = 0 := by
      have e : B * (1 - PowerSeries.X * B ^ 4) - (1 + PowerSeries.X * B ^ 4)
          = B - (1 + PowerSeries.X * B ^ 4 + PowerSeries.X * B ^ 5) := by ring
      rw [e, ← h2, sub_self]
    exact sub_eq_zero.mp h
  have hpow : (B * (1 - PowerSeries.X * B ^ 4)) ^ 4 = (1 + PowerSeries.X * B ^ 4) ^ 4 := by
    rw [hB]
  have hZ : (PowerSeries.X * B ^ 4) * (1 - PowerSeries.X * B ^ 4) ^ 4 =
      PowerSeries.X * (1 + PowerSeries.X * B ^ 4) ^ 4 := by
    have hp : B ^ 4 * (1 - PowerSeries.X * B ^ 4) ^ 4 = (1 + PowerSeries.X * B ^ 4) ^ 4 := by
      rw [← hpow]
      ring
    calc (PowerSeries.X * B ^ 4) * (1 - PowerSeries.X * B ^ 4) ^ 4
        = PowerSeries.X * (B ^ 4 * (1 - PowerSeries.X * B ^ 4) ^ 4) := by ring
      _ = PowerSeries.X * (1 + PowerSeries.X * B ^ 4) ^ 4 := by rw [hp]
  have hy : (PowerSeries.X * A) * (1 - PowerSeries.X * A) ^ 4 =
      PowerSeries.X * (1 + PowerSeries.X * A) ^ 4 := h1
  have hkey : PowerSeries.X * A = PowerSeries.X * B ^ 4 :=
    OMA.quartic_unique (by simp) (by simp) hy hZ
  exact mul_left_cancel₀ (PowerSeries.X_ne_zero) hkey
