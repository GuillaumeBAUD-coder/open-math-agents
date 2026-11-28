import OMAStatements.S_oeis_a380128
import Mathlib

namespace A380128Proof

open PowerSeries OMA.S_oeis_a380128

/-- G k N r = [x^r] (1+x)^N (1+x)^(-(k+1)). -/
def G (k N r : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (r + 1), (-1 : ℤ) ^ i * (N.choose (r - i) : ℤ) * ((k + i).choose i : ℤ)

lemma G_zero (k N : ℕ) : G k N 0 = 1 := by simp [G]

lemma G_pascal (k N r : ℕ) : G k (N + 1) (r + 1) = G k N (r + 1) + G k N r := by
  unfold G
  rw [Finset.sum_range_succ, Finset.sum_range_succ _ (r + 1), add_right_comm,
    ← Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have : r + 1 - i = (r - i) + 1 := by omega
    rw [this, Nat.choose_succ_succ]
    push_cast
    ring
  · simp

lemma G_down (k N r : ℕ) : G k N (r + 1) = G (k + 1) N (r + 1) + G (k + 1) N r := by
  unfold G
  rw [Finset.sum_range_succ', Finset.sum_range_succ' _ (r + 1)]
  have h1 : ∀ j ∈ Finset.range (r + 1),
      (-1 : ℤ) ^ (j + 1) * (N.choose (r + 1 - (j + 1)) : ℤ) * ((k + (j + 1)).choose (j + 1) : ℤ)
      = (-1 : ℤ) ^ (j + 1) * (N.choose (r + 1 - (j + 1)) : ℤ)
          * ((k + 1 + (j + 1)).choose (j + 1) : ℤ)
        + (-1 : ℤ) ^ j * (N.choose (r - j) : ℤ) * ((k + 1 + j).choose j : ℤ) := by
    intro j _
    have e1 : r + 1 - (j + 1) = r - j := by omega
    have e2 : k + 1 + (j + 1) = (k + 1 + j) + 1 := by omega
    have e3 : k + (j + 1) = k + 1 + j := by omega
    rw [e1, e2, Nat.choose_succ_succ, e3]
    push_cast
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  simp
  ring

lemma G_shift (k N r : ℕ) : G (k + 1) (N + 1) r = G k N r := by
  cases r with
  | zero => simp [G_zero]
  | succ r => rw [G_pascal, G_down k N r]

lemma G0_alt (N r : ℕ) : G 0 N (r + 1) = (N.choose (r + 1) : ℤ) - G 0 N r := by
  unfold G
  rw [Finset.sum_range_succ']
  have key : ∑ j ∈ Finset.range (r + 1),
      (-1 : ℤ) ^ (j + 1) * (N.choose (r + 1 - (j + 1)) : ℤ) * ((0 + (j + 1)).choose (j + 1) : ℤ)
      = - ∑ i ∈ Finset.range (r + 1), (-1 : ℤ) ^ i * (N.choose (r - i) : ℤ) * ((0 + i).choose i : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have e1 : r + 1 - (j + 1) = r - j := by omega
    rw [e1]
    simp
    ring
  rw [key]
  simp
  ring

lemma G0 (N r : ℕ) : G 0 (N + 1) (r + 1) = (N.choose (r + 1) : ℤ) := by
  rw [G_pascal, G0_alt]; ring

lemma G1 (N r : ℕ) : G 1 (N + 2) (r + 1) = (N.choose (r + 1) : ℤ) := by
  rw [G_shift, G0]

lemma G_step (k m : ℕ) :
    G (k + 2) (2 * (m + 1)) (m + 1) = G (k + 1) (2 * (m + 1)) (m + 1) - G k (2 * m) m := by
  have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
  rw [e, G_shift (k + 1), G_shift k, G_shift k, G_pascal]
  ring

/-! Series part. -/

lemma hC : catGF = 1 + X * catGF ^ 2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
  have e : PowerSeries.map (Nat.castRingHom ℚ) catalanSeries = catGF := by
    ext n; simp [catGF, catalanSeries]
  rw [map_add, map_mul, map_pow, e, map_one, PowerSeries.map_X] at h
  linear_combination (-1 : PowerSeries ℚ) * h

lemma hB : cbGF = derivative ℚ (X * catGF) := by
  ext n
  rw [coeff_derivative, coeff_succ_X_mul]
  simp only [cbGF, catGF, coeff_mk]
  rw [← succ_mul_catalan_eq_centralBinom]
  push_cast
  ring

lemma hB' : cbGF = 1 + 2 * (X * catGF) * cbGF := by
  have h : X * catGF = X + (X * catGF) ^ 2 := by
    conv_lhs => rw [hC]
    ring
  have h2 := congrArg (derivative ℚ) h
  rw [map_add, derivative_X, derivative_pow, ← hB] at h2
  simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat] at h2
  exact h2

lemma hCi : catGF⁻¹ = 1 - X * catGF := by
  have h0 : constantCoeff catGF ≠ 0 := by simp [catGF]
  have h1 : catGF * (1 - X * catGF) = 1 := by
    have := hC
    linear_combination this
  have h2 : catGF⁻¹ * catGF = 1 := PowerSeries.inv_mul_cancel _ h0
  calc catGF⁻¹ = catGF⁻¹ * (catGF * (1 - X * catGF)) := by rw [h1, mul_one]
    _ = (catGF⁻¹ * catGF) * (1 - X * catGF) := by ring
    _ = 1 - X * catGF := by rw [h2, one_mul]

lemma hCi2 : catGF⁻¹ ^ 2 = catGF⁻¹ - X := by
  have h0 : constantCoeff catGF ≠ 0 := by simp [catGF]
  have h2 : catGF⁻¹ * catGF = 1 := PowerSeries.inv_mul_cancel _ h0
  calc catGF⁻¹ ^ 2 = catGF⁻¹ * catGF⁻¹ := by ring
    _ = catGF⁻¹ * (1 - X * catGF) := by rw [← hCi]
    _ = catGF⁻¹ - X * (catGF⁻¹ * catGF) := by ring
    _ = catGF⁻¹ - X := by rw [h2, mul_one]

lemma hE1 : 2 * (cbGF * catGF⁻¹) = cbGF + 1 := by
  rw [hCi]
  have := hB'
  linear_combination this

/-- E j = B * (1/C)^j. -/
noncomputable def E (j : ℕ) : PowerSeries ℚ := cbGF * catGF⁻¹ ^ j

lemma E_rec (j : ℕ) : E (j + 2) = E (j + 1) - X * E j := by
  unfold E
  rw [pow_add, hCi2, pow_succ]
  ring

lemma centralBinom_succ_eq (m : ℕ) : Nat.centralBinom (m + 1) = 2 * (2 * m + 1).choose (m + 1) := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
  rw [e, Nat.choose_succ_succ, Nat.choose_symm_half]
  ring

lemma E1_coeff (m : ℕ) : coeff m (E 1) = (G 0 (2 * m) m : ℚ) := by
  have h : (2 : ℚ) * coeff m (E 1) = coeff m (cbGF + 1) := by
    have hE : E 1 = cbGF * catGF⁻¹ := by simp [E]
    rw [← hE1, hE, ← map_ofNat (PowerSeries.C (R := ℚ)) 2, coeff_C_mul]
  cases m with
  | zero =>
    rw [G_zero]
    simp [cbGF] at h
    simp
    linarith
  | succ m =>
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [e, G0]
    simp only [map_add, cbGF, coeff_mk, coeff_one] at h
    rw [centralBinom_succ_eq] at h
    simp at h
    push_cast
    linarith

lemma E2_coeff (m : ℕ) : coeff m (E 2) = (G 1 (2 * m) m : ℚ) := by
  rw [E_rec, map_sub]
  cases m with
  | zero =>
    rw [E1_coeff, G_zero, G_zero]
    simp
  | succ m =>
    rw [coeff_succ_X_mul, E1_coeff]
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [e, G0, G1]
    simp only [E, pow_zero, mul_one, cbGF, coeff_mk]
    have h := Nat.choose_succ_succ (2 * m) m
    rw [Nat.centralBinom_eq_two_mul_choose]
    rw [h]
    push_cast
    ring

lemma E_coeff (k : ℕ) : ∀ m, coeff m (E (k + 1)) = (G k (2 * m) m : ℚ) := by
  induction k using Nat.twoStepInduction with
  | zero => exact E1_coeff
  | one => exact E2_coeff
  | more k ih1 ih2 =>
    intro m
    rw [E_rec, map_sub]
    cases m with
    | zero =>
      rw [ih2, G_zero, G_zero]
      simp
    | succ m =>
      rw [coeff_succ_X_mul, ih2, ih1, G_step]
      push_cast
      ring

lemma T_eq (n k : ℕ) (h : k ≤ n) : T n k = coeff (n - k) (E (k + 1)) := by
  unfold T E
  have : catGF⁻¹ * cbGF * (X * catGF⁻¹) ^ k = X ^ k * (cbGF * catGF⁻¹ ^ (k + 1)) := by ring
  rw [this, coeff_X_pow_mul', if_pos h]

end A380128Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a380128.main := by
  intro n k h
  rw [A380128Proof.T_eq n k h, A380128Proof.E_coeff]
  unfold A380128Proof.G
  have e : 2 * n - 2 * k = 2 * (n - k) := by omega
  rw [e]
  push_cast
  rfl
