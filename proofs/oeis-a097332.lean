import OMAStatements.S_oeis_a097332
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Binomial

-- Problem: A097332: D-finite recurrence from generating function
-- Credit: @Luckylamb666

open PowerSeries OMA.S_oeis_a097332

namespace OMA_A097332_Proof

lemma binomial_half_sq :
    PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) * PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) =
      1 + (X : PowerSeries ℚ) := by
  rw [← PowerSeries.binomialSeries_add]
  have h1 : (1 / 2 : ℚ) + (1 / 2 : ℚ) = 1 := by norm_num
  rw [h1]
  ext n
  rcases n with _ | _ | n
  · simp
  · simp
  · simp only [map_add, coeff_one, coeff_X, PowerSeries.binomialSeries_coeff]
    rw [show (1 : ℚ) = ((1 : ℕ) : ℚ) from rfl, Ring.choose_natCast]
    simp [Nat.choose_eq_zero_of_lt (by omega : 1 < n + 1 + 1)]

lemma rootSeries_sq :
    rootSeries ^ 2 = (1 - 2 * X - 3 * X ^ 2 : PowerSeries ℚ) := by
  unfold rootSeries
  have h1 : PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) ^ 2 = 1 + (X : PowerSeries ℚ) := by
    rw [sq, binomial_half_sq]
  have h2 : (rescale (-3 : ℚ) (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ))) ^ 2 =
      1 - 3 * (X : PowerSeries ℚ) := by
    rw [← map_pow, h1, map_add, map_one, rescale_X, map_neg, map_ofNat]
    ring
  calc
    (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) *
        rescale (-3 : ℚ) (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ))) ^ 2
      = PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) ^ 2 *
          (rescale (-3 : ℚ) (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ))) ^ 2 := mul_pow _ _ 2
    _ = (1 + X) * (1 - 3 * X) := by rw [h1, h2]
    _ = 1 - 2 * X - 3 * X ^ 2 := by ring

lemma constantCoeff_rootSeries : constantCoeff rootSeries = 1 := by
  unfold rootSeries
  rw [map_mul, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
  simp

lemma isUnit_one_sub_X : IsUnit (1 - (X : PowerSeries ℚ)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

lemma isUnit_denom : IsUnit (1 - X + rootSeries) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp [constantCoeff_rootSeries]

lemma linear_rel :
    2 * X * (1 - X) * generatingSeries = 1 + X - rootSeries := by
  have hinv1 : (1 - (X : PowerSeries ℚ)) * (1 - X)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp)
  have hinv2 : (1 - X + rootSeries) * (1 - X + rootSeries)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp [constantCoeff_rootSeries])
  have hdiff : (1 - X + rootSeries) * (1 - X - rootSeries) = 4 * (X : PowerSeries ℚ) ^ 2 := by
    calc
      (1 - X + rootSeries) * (1 - X - rootSeries) = (1 - X) ^ 2 - rootSeries ^ 2 := by ring
      _ = (1 - X) ^ 2 - (1 - 2 * X - 3 * X ^ 2) := by rw [rootSeries_sq]
      _ = 4 * X ^ 2 := by ring
  have h2x_ne : (2 * X : PowerSeries ℚ) ≠ 0 := by
    intro h
    have hc := congrArg (coeff 1) h
    rw [show (2 : PowerSeries ℚ) = 1 + 1 by ring, add_mul, one_mul, map_add, coeff_X] at hc
    norm_num at hc
  have hfrac : 2 * X * (2 * X * (1 - X + rootSeries)⁻¹) = 1 - X - rootSeries := by
    apply mul_left_cancel₀ h2x_ne
    calc
      2 * X * (2 * X * (2 * X * (1 - X + rootSeries)⁻¹))
        = (4 * X ^ 2) * (2 * X * (1 - X + rootSeries)⁻¹) := by ring
      _ = ((1 - X + rootSeries) * (1 - X - rootSeries)) * (2 * X * (1 - X + rootSeries)⁻¹) := by
          rw [hdiff]
      _ = 2 * X * (1 - X - rootSeries) * ((1 - X + rootSeries) * (1 - X + rootSeries)⁻¹) := by
          ring
      _ = 2 * X * (1 - X - rootSeries) := by rw [hinv2, mul_one]
  unfold generatingSeries
  calc
    2 * X * (1 - X) * ((1 - X)⁻¹ * (1 + 2 * X * (1 - X + rootSeries)⁻¹))
      = ((1 - X) * (1 - X)⁻¹) * (2 * X + 2 * X * (2 * X * (1 - X + rootSeries)⁻¹)) := by ring
    _ = 1 * (2 * X + (1 - X - rootSeries)) := by rw [hinv1, hfrac]
    _ = 1 + X - rootSeries := by ring

lemma two_ne_zero_ps : (2 : PowerSeries ℚ) ≠ 0 := by
  intro h
  have hc := congrArg (coeff 0) h
  rw [show (2 : PowerSeries ℚ) = 1 + 1 by ring, map_add, coeff_zero_one] at hc
  norm_num at hc

lemma neg_two_ne_zero_ps : (-2 : PowerSeries ℚ) ≠ 0 := by
  intro h
  have hc := congrArg (coeff 0) h
  rw [map_neg, show (2 : PowerSeries ℚ) = 1 + 1 by ring, map_add, coeff_zero_one] at hc
  norm_num at hc

lemma derivative_two_ps : derivative ℚ (2 : PowerSeries ℚ) = 0 := by
  rw [show (2 : PowerSeries ℚ) = 1 + 1 by ring, map_add, Derivation.map_one_eq_zero, add_zero]

lemma derivative_three_ps : derivative ℚ (3 : PowerSeries ℚ) = 0 := by
  rw [show (3 : PowerSeries ℚ) = 1 + 1 + 1 by ring, map_add, map_add, Derivation.map_one_eq_zero]
  simp

lemma rootSeries_ode :
    (1 - 2 * X - 3 * X ^ 2) * derivative ℚ rootSeries + (1 + 3 * X) * rootSeries = 0 := by
  have hsq : derivative ℚ (rootSeries ^ 2) = derivative ℚ (1 - 2 * X - 3 * X ^ 2 : PowerSeries ℚ) :=
    congrArg (derivative ℚ) rootSeries_sq
  have hLHS : derivative ℚ (rootSeries ^ 2) = 2 * rootSeries * derivative ℚ rootSeries := by
    rw [sq, Derivation.leibniz]
    ring
  have hRHS : derivative ℚ (1 - 2 * X - 3 * X ^ 2 : PowerSeries ℚ) = -2 - 6 * X := by
    simp [sq, Derivation.leibniz, derivative_two_ps, derivative_three_ps]
    ring
  have h2 : 2 * (rootSeries * derivative ℚ rootSeries + (1 + 3 * X)) = 0 := by
    have : 2 * rootSeries * derivative ℚ rootSeries = -2 - 6 * X := by rw [← hLHS, hsq, hRHS]
    linear_combination this
  have h1 : rootSeries * derivative ℚ rootSeries + (1 + 3 * X) = 0 := by
    apply mul_left_cancel₀ two_ne_zero_ps
    simpa using h2
  calc
    (1 - 2 * X - 3 * X ^ 2) * derivative ℚ rootSeries + (1 + 3 * X) * rootSeries
      = rootSeries ^ 2 * derivative ℚ rootSeries + (1 + 3 * X) * rootSeries := by rw [rootSeries_sq]
    _ = rootSeries * (rootSeries * derivative ℚ rootSeries + (1 + 3 * X)) := by ring
    _ = 0 := by rw [h1, mul_zero]

lemma gen_ode :
    (3 * X ^ 4 - X ^ 3 - 3 * X ^ 2 + X) * derivative ℚ generatingSeries +
    (3 * X ^ 3 + 3 * X ^ 2 - 3 * X + 1) * generatingSeries - (1 + X) = 0 := by
  have hS : rootSeries = 1 + X - 2 * X * (1 - X) * generatingSeries := by
    linear_combination linear_rel
  have hdS : derivative ℚ rootSeries =
      1 - (2 - 4 * X) * generatingSeries - (2 * X - 2 * X ^ 2) * derivative ℚ generatingSeries := by
    rw [hS]
    simp [sq, Derivation.leibniz, derivative_two_ps, derivative_three_ps]
    ring
  have h0 := rootSeries_ode
  rw [hdS, hS] at h0
  have h2 : (-2 : PowerSeries ℚ) *
      ((3 * X ^ 4 - X ^ 3 - 3 * X ^ 2 + X) * derivative ℚ generatingSeries +
       (3 * X ^ 3 + 3 * X ^ 2 - 3 * X + 1) * generatingSeries - (1 + X)) = 0 := by
    linear_combination h0
  apply mul_left_cancel₀ neg_two_ne_zero_ps
  simpa using h2

lemma coeff_X_pow_mul (m d : ℕ) (f : PowerSeries ℚ) (h : d ≤ m) :
    coeff m (X ^ d * f) = coeff (m - d) f := by
  induction d generalizing m with
  | zero => simp
  | succ d ih =>
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0) with ⟨m', rfl⟩
    rw [pow_succ', mul_assoc, coeff_succ_X_mul, ih m' (by omega), Nat.succ_sub_succ]

end OMA_A097332_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a097332.main := by
  intro k
  have hc := congrArg (coeff (k + 3)) OMA_A097332_Proof.gen_ode
  simp only [map_zero, map_sub, map_add, coeff_one, coeff_X] at hc
  have h1 : (3 * X ^ 4 - X ^ 3 - 3 * X ^ 2 + X) * derivative ℚ generatingSeries =
      C 3 * (X ^ 4 * derivative ℚ generatingSeries) -
      (X ^ 3 * derivative ℚ generatingSeries) -
      C 3 * (X ^ 2 * derivative ℚ generatingSeries) +
      (X * derivative ℚ generatingSeries) := by
    simp only [map_ofNat]
    ring
  have h2 : (3 * X ^ 3 + 3 * X ^ 2 - 3 * X + 1) * generatingSeries =
      C 3 * (X ^ 3 * generatingSeries) +
      C 3 * (X ^ 2 * generatingSeries) -
      C 3 * (X * generatingSeries) +
      generatingSeries := by
    simp only [map_ofNat]
    ring
  rw [h1, h2] at hc
  simp only [map_add, map_sub, coeff_C_mul] at hc
  have hd4 : coeff (k + 3) (X ^ 4 * derivative ℚ generatingSeries) =
      if k = 0 then 0 else ((k : ℚ)) * a k := by
    cases k with
    | zero =>
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ', mul_assoc, coeff_succ_X_mul,
          show (3 : ℕ) = 2 + 1 from rfl, pow_succ', mul_assoc, coeff_succ_X_mul,
          show (2 : ℕ) = 1 + 1 from rfl, pow_succ', mul_assoc, coeff_succ_X_mul,
          pow_one, coeff_zero_X_mul]
      simp
    | succ k' =>
      rw [OMA_A097332_Proof.coeff_X_pow_mul (k' + 4) 4 _ (by omega)]
      simp [coeff_derivative, a]
      ring
  have hd3 : coeff (k + 3) (X ^ 3 * derivative ℚ generatingSeries) = ((k : ℚ) + 1) * a (k + 1) := by
    rw [OMA_A097332_Proof.coeff_X_pow_mul (k + 3) 3 _ (by omega)]
    simp [coeff_derivative, a]
    ring
  have hd2 : coeff (k + 3) (X ^ 2 * derivative ℚ generatingSeries) = ((k : ℚ) + 2) * a (k + 2) := by
    rw [OMA_A097332_Proof.coeff_X_pow_mul (k + 3) 2 _ (by omega)]
    simp [coeff_derivative, a]
    ring
  have hd1 : coeff (k + 3) (X * derivative ℚ generatingSeries) = ((k : ℚ) + 3) * a (k + 3) := by
    rw [coeff_succ_X_mul]
    simp [coeff_derivative, a]
    ring
  have hg3 : coeff (k + 3) (X ^ 3 * generatingSeries) = a k := by
    rw [OMA_A097332_Proof.coeff_X_pow_mul (k + 3) 3 _ (by omega)]
    simp [a]
  have hg2 : coeff (k + 3) (X ^ 2 * generatingSeries) = a (k + 1) := by
    rw [OMA_A097332_Proof.coeff_X_pow_mul (k + 3) 2 _ (by omega)]
    simp [a]
  have hg1 : coeff (k + 3) (X * generatingSeries) = a (k + 2) := by
    rw [coeff_succ_X_mul]
    rfl
  have hg0 : coeff (k + 3) generatingSeries = a (k + 3) := rfl
  have hconst : (if k + 3 = 0 then (1 : ℚ) else 0) + (if k + 3 = 1 then (1 : ℚ) else 0) = 0 := by
    simp
  rw [hd4, hd3, hd2, hd1, hg3, hg2, hg1, hg0] at hc
  dsimp only
  cases k with
  | zero =>
    simp at hc ⊢
    linarith
  | succ k' =>
    simp at hc ⊢
    linarith
