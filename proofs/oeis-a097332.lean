import OMAStatements.S_oeis_a097332
import Mathlib

namespace R097332

open OMA.S_oeis_a097332 PowerSeries

lemma coeff_two_mul' (n : ℕ) (f : PowerSeries ℚ) : coeff n (2 * f) = 2 * coeff n f := by
  rw [two_mul, two_mul, map_add]

lemma hB : PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) * PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) = 1 + X := by
  rw [← binomialSeries_add]
  have h := binomialSeries_nat (R := ℚ) (A := ℚ) 1
  norm_num at h ⊢
  exact h

lemma hsq : rootSeries * rootSeries = (1 + X) * (1 + C (-3 : ℚ) * X) := by
  have e : rootSeries * rootSeries =
      (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) * PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) *
        rescale (-3 : ℚ) (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) * PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) := by
    rw [map_mul]; unfold rootSeries; ring
  rw [e, hB, map_add, map_one, rescale_X]

lemma hc : (C (-3 : ℚ) : PowerSeries ℚ) = -3 := by
  rw [map_neg, map_ofNat]

lemma hR0 : constantCoeff rootSeries = 1 := by
  have h : constantCoeff (rescale (-3 : ℚ) (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ))) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
    simp
  show constantCoeff (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) *
    rescale (-3 : ℚ) (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ))) = 1
  rw [map_mul, h, binomialSeries_constantCoeff, one_mul]

lemma hDP : PowerSeries.derivative ℚ ((1 + X) * (1 + C (-3 : ℚ) * X)) =
    (1 + X) * C (-3 : ℚ) + (1 + C (-3 : ℚ) * X) := by
  simp only [Derivation.leibniz, map_add, Derivation.map_one_eq_zero, derivative_X,
    derivative_C, smul_eq_mul]
  ring

lemma hQ : 2 * PowerSeries.derivative ℚ rootSeries
    + 2 * (X * PowerSeries.derivative ℚ rootSeries)
    + 2 * (X * (C (-3 : ℚ) * PowerSeries.derivative ℚ rootSeries))
    + 2 * (X * (X * (C (-3 : ℚ) * PowerSeries.derivative ℚ rootSeries)))
    = rootSeries + C (-3 : ℚ) * rootSeries + X * (C (-3 : ℚ) * rootSeries)
      + X * (C (-3 : ℚ) * rootSeries) := by
  have hD : PowerSeries.derivative ℚ (rootSeries * rootSeries) =
      rootSeries * PowerSeries.derivative ℚ rootSeries +
        rootSeries * PowerSeries.derivative ℚ rootSeries := by
    rw [Derivation.leibniz, smul_eq_mul]
  have E : 2 * ((1 + X) * (1 + C (-3 : ℚ) * X)) * PowerSeries.derivative ℚ rootSeries =
      rootSeries * ((1 + X) * C (-3 : ℚ) + (1 + C (-3 : ℚ) * X)) := by
    rw [← hDP, ← hsq, hD]; ring
  linear_combination E

lemma hODE (n : ℕ) : ((n : ℚ) + 3) * coeff (n + 3) rootSeries =
    (2 * (n : ℚ) + 3) * coeff (n + 2) rootSeries + 3 * (n : ℚ) * coeff (n + 1) rootSeries := by
  have h := congrArg (coeff (n + 1 + 1)) hQ
  simp only [map_add, coeff_two_mul', coeff_succ_X_mul, coeff_C_mul, coeff_derivative] at h
  push_cast at h
  have e3 : coeff (n + 1 + 1 + 1) rootSeries = coeff (n + 3) rootSeries := rfl
  have e2 : coeff (n + 1 + 1) rootSeries = coeff (n + 2) rootSeries := rfl
  rw [e3, e2] at h
  linear_combination (1 / 2 : ℚ) * h

lemma hS : (1 - X + rootSeries) * (1 - X + rootSeries)⁻¹ = 1 := by
  apply PowerSeries.mul_inv_cancel
  rw [map_add, map_sub, map_one, constantCoeff_X, hR0]
  norm_num

lemma hK : 2 * X * ((1 - X) * generatingSeries) = 1 + X - rootSeries := by
  have h1 : (1 - X : PowerSeries ℚ) * (1 - X)⁻¹ = 1 := by
    apply PowerSeries.mul_inv_cancel
    rw [map_sub, map_one, constantCoeff_X]
    norm_num
  have hH : (1 - X) * generatingSeries = 1 + 2 * X * (1 - X + rootSeries)⁻¹ := by
    unfold generatingSeries
    rw [← mul_assoc, h1, one_mul]
  rw [hH]
  linear_combination (4 * X ^ 2 * (1 - X + rootSeries)⁻¹ -
      (X - 1 + rootSeries + 4 * X ^ 2 * (1 - X + rootSeries)⁻¹)) * hS +
    (1 - X + rootSeries)⁻¹ * hsq + (1 - X + rootSeries)⁻¹ * (X + X ^ 2) * hc

lemma hA (n : ℕ) : 2 * a (n + 1) - 2 * a n = - coeff (n + 2) rootSeries := by
  have K : X * (2 * generatingSeries - 2 * (X * generatingSeries)) = 1 + X - rootSeries := by
    rw [← hK]; ring
  have h := congrArg (coeff (n + 1 + 1)) K
  simp only [coeff_succ_X_mul, map_sub, coeff_two_mul', map_add, coeff_one, coeff_X] at h
  simp at h
  unfold a
  linear_combination h

end R097332

open R097332 in
theorem OMA.solution : type_of% @OMA.S_oeis_a097332.main := by
  intro k
  dsimp only
  have h1 : 2 * OMA.S_oeis_a097332.a (k + 3) - 2 * OMA.S_oeis_a097332.a (k + 2) =
      - PowerSeries.coeff (k + 4) OMA.S_oeis_a097332.rootSeries := hA (k + 2)
  have h2 : 2 * OMA.S_oeis_a097332.a (k + 2) - 2 * OMA.S_oeis_a097332.a (k + 1) =
      - PowerSeries.coeff (k + 3) OMA.S_oeis_a097332.rootSeries := hA (k + 1)
  have h3 : 2 * OMA.S_oeis_a097332.a (k + 1) - 2 * OMA.S_oeis_a097332.a k =
      - PowerSeries.coeff (k + 2) OMA.S_oeis_a097332.rootSeries := hA k
  have h4 : ((k : ℚ) + 1 + 3) * PowerSeries.coeff (k + 4) OMA.S_oeis_a097332.rootSeries =
      (2 * ((k : ℚ) + 1) + 3) * PowerSeries.coeff (k + 3) OMA.S_oeis_a097332.rootSeries +
        3 * ((k : ℚ) + 1) * PowerSeries.coeff (k + 2) OMA.S_oeis_a097332.rootSeries := by
    have := hODE (k + 1)
    push_cast at this
    exact this
  linear_combination (-(1 : ℚ) / 2) * h4 + (((k : ℚ) + 4) / 2) * h1 +
    (-(2 * (k : ℚ) + 5) / 2) * h2 + (-(3 * ((k : ℚ) + 1)) / 2) * h3
