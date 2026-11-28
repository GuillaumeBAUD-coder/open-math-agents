import OMAStatements.S_oeis_a162171
import Mathlib

open PowerSeries

namespace A162171Proof

lemma constCoeff_cos : constantCoeff (PowerSeries.cos ℚ) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [PowerSeries.cos]

lemma rescale_cos : rescale (-1 : ℚ) (PowerSeries.cos ℚ) = PowerSeries.cos ℚ := by
  ext n
  rw [coeff_rescale]
  simp only [PowerSeries.cos, coeff_mk]
  split_ifs with h
  · rw [h.neg_one_pow, one_mul]
  · rw [mul_zero]

lemma rescale_sin : rescale (-1 : ℚ) (PowerSeries.sin ℚ) = -PowerSeries.sin ℚ := by
  ext n
  rw [coeff_rescale, map_neg]
  simp only [PowerSeries.sin, coeff_mk]
  split_ifs with h
  · simp
  · rw [(Nat.not_even_iff_odd.mp h).neg_one_pow]; ring

lemma rescale_cosinv : rescale (-1 : ℚ) (PowerSeries.cos ℚ)⁻¹ = (PowerSeries.cos ℚ)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by rw [constCoeff_cos]; norm_num)]
  have h := PowerSeries.mul_inv_cancel (PowerSeries.cos ℚ) (by rw [constCoeff_cos]; norm_num)
  have h2 := congrArg (rescale (-1 : ℚ)) h
  rw [map_mul, map_one, rescale_cos] at h2
  rw [mul_comm]; exact h2

lemma coeff_odd_of_even {f : PowerSeries ℚ} (hf : rescale (-1 : ℚ) f = f) {n : ℕ}
    (hn : n % 2 = 1) : coeff n f = 0 := by
  have h := congrArg (coeff n) hf
  rw [coeff_rescale, (Nat.odd_iff.mpr hn).neg_one_pow] at h
  linarith

lemma coeff_even_of_odd {f : PowerSeries ℚ} (hf : rescale (-1 : ℚ) f = -f) {n : ℕ}
    (hn : n % 2 = 0) : coeff n f = 0 := by
  have h := congrArg (coeff n) hf
  rw [coeff_rescale, (Nat.even_iff.mpr hn).neg_one_pow, map_neg] at h
  linarith

lemma rescale_X2 : rescale (-1 : ℚ) ((X : PowerSeries ℚ) ^ 2) = X ^ 2 := by
  rw [map_pow, rescale_X]; simp

lemma rescale_P : rescale (-1 : ℚ) ((X : PowerSeries ℚ) ^ 2 * (PowerSeries.cos ℚ)⁻¹) =
    X ^ 2 * (PowerSeries.cos ℚ)⁻¹ := by
  rw [map_mul, rescale_X2, rescale_cosinv]

lemma rescale_Q : rescale (-1 : ℚ) ((X : PowerSeries ℚ) ^ 2 * PowerSeries.sin ℚ * (PowerSeries.cos ℚ)⁻¹) =
    -(X ^ 2 * PowerSeries.sin ℚ * (PowerSeries.cos ℚ)⁻¹) := by
  rw [map_mul, map_mul, rescale_X2, rescale_cosinv, rescale_sin]; ring

lemma coeff_CS (i j : ℕ) (hj : j % 2 = 0) (hji : j ≤ i) :
    coeff (i - j) (PowerSeries.cos ℚ - PowerSeries.sin ℚ) =
      ((-1 : ℚ) ^ ((i + j + 1) / 2)) / ((i - j).factorial : ℚ) := by
  rw [map_sub]
  simp only [PowerSeries.cos, PowerSeries.sin, coeff_mk]
  obtain ⟨p, hp⟩ : ∃ p, i = j + p := ⟨i - j, by omega⟩
  subst hp
  have hjj : j + p - j = p := by omega
  rw [hjj]
  obtain ⟨k, hk⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
  subst hk
  rcases Nat.even_or_odd p with ⟨q, hq⟩ | ⟨q, hq⟩
  · subst hq
    have e1 : (2 * k + (q + q) + 2 * k + 1) / 2 = 2 * (k) + q := by omega
    have e2 : (q + q) / 2 = q := by omega
    rw [if_pos ⟨q, rfl⟩, if_pos ⟨q, rfl⟩, e1, e2, pow_add, pow_mul]
    simp
  · subst hq
    have hne : ¬ Even (2 * q + 1) := Nat.not_even_iff_odd.mpr ⟨q, rfl⟩
    have e1 : (2 * k + (2 * q + 1) + 2 * k + 1) / 2 = 2 * k + q + 1 := by omega
    have e2 : (2 * q + 1) / 2 = q := by omega
    rw [if_neg hne, if_neg hne, e1, e2, pow_add, pow_add, pow_mul]
    simp
    ring

open OMA.S_oeis_a162171 in
lemma term_eq (i j : ℕ) (hji : j ≤ i) :
    (A162169 (i + 1) (j + 1) : ℚ) * ((j.factorial : ℚ) / 2 *
      coeff j ((X : PowerSeries ℚ) ^ 2 * ((PowerSeries.cos ℚ)⁻¹ + PowerSeries.sin ℚ * (PowerSeries.cos ℚ)⁻¹))) =
    (i.factorial : ℚ) / 2 *
      (coeff j ((X : PowerSeries ℚ) ^ 2 * (PowerSeries.cos ℚ)⁻¹) *
          coeff (i - j) (PowerSeries.cos ℚ - PowerSeries.sin ℚ) +
        if j = i then coeff j ((X : PowerSeries ℚ) ^ 2 * PowerSeries.sin ℚ * (PowerSeries.cos ℚ)⁻¹)
        else 0) := by
  have hw : (X : PowerSeries ℚ) ^ 2 * ((PowerSeries.cos ℚ)⁻¹ + PowerSeries.sin ℚ * (PowerSeries.cos ℚ)⁻¹) =
      X ^ 2 * (PowerSeries.cos ℚ)⁻¹ + X ^ 2 * PowerSeries.sin ℚ * (PowerSeries.cos ℚ)⁻¹ := by ring
  rw [hw, map_add]
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · have hQ := coeff_even_of_odd rescale_Q hj
    rw [hQ, add_zero, ite_self, add_zero, coeff_CS i j hj hji]
    have hA : (A162169 (i + 1) (j + 1) : ℚ) = (i.choose j : ℚ) * (-1) ^ ((i + j + 1) / 2) := by
      have h1 : (j + 1) % 2 = 1 := by omega
      simp only [A162169, h1, if_true, Nat.add_sub_cancel]
      push_cast
      congr 2; omega
    rw [hA]
    have hc := Nat.choose_mul_factorial_mul_factorial hji
    have hc' : (i.choose j : ℚ) * (j.factorial : ℚ) * ((i - j).factorial : ℚ) = (i.factorial : ℚ) := by
      exact_mod_cast hc
    have hf : ((i - j).factorial : ℚ) ≠ 0 := by positivity
    field_simp
    rw [← hc']
    ring
  · have hP := coeff_odd_of_even rescale_P hj
    rw [hP, zero_add, zero_mul, zero_add]
    have hA : (A162169 (i + 1) (j + 1) : ℚ) = if j = i then 1 else 0 := by
      have h1 : ¬ (j + 1) % 2 = 1 := by omega
      simp only [A162169, h1, if_false]
      by_cases h : j = i
      · subst h; simp
      · rw [if_neg (by omega), if_neg h]; simp
    rw [hA]
    split_ifs with h
    · subst h; ring
    · ring

lemma key (i : ℕ) :
    ∑ j ∈ Finset.range (i + 1), (OMA.S_oeis_a162171.A162169 (i + 1) (j + 1) : ℚ) *
      ((j.factorial : ℚ) / 2 *
        coeff j ((X : PowerSeries ℚ) ^ 2 * ((PowerSeries.cos ℚ)⁻¹ + PowerSeries.sin ℚ * (PowerSeries.cos ℚ)⁻¹))) =
      if i = 2 then 1 else 0 := by
  rw [Finset.sum_congr rfl fun j hj => term_eq i j (by simp at hj; omega)]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (i + 1)) i,
    if_pos (by simp)]
  have hmul : ∑ j ∈ Finset.range (i + 1), coeff j ((X : PowerSeries ℚ) ^ 2 * (PowerSeries.cos ℚ)⁻¹) *
      coeff (i - j) (PowerSeries.cos ℚ - PowerSeries.sin ℚ) =
      coeff i ((X : PowerSeries ℚ) ^ 2 * (PowerSeries.cos ℚ)⁻¹ * (PowerSeries.cos ℚ - PowerSeries.sin ℚ)) := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => coeff a ((X : PowerSeries ℚ) ^ 2 * (PowerSeries.cos ℚ)⁻¹) *
        coeff b (PowerSeries.cos ℚ - PowerSeries.sin ℚ))]
  rw [hmul, ← map_add]
  have hinv := PowerSeries.mul_inv_cancel (PowerSeries.cos ℚ) (by rw [constCoeff_cos]; norm_num)
  have hid : (X : PowerSeries ℚ) ^ 2 * (PowerSeries.cos ℚ)⁻¹ * (PowerSeries.cos ℚ - PowerSeries.sin ℚ) +
      X ^ 2 * PowerSeries.sin ℚ * (PowerSeries.cos ℚ)⁻¹ = X ^ 2 := by
    calc _ = X ^ 2 * (PowerSeries.cos ℚ * (PowerSeries.cos ℚ)⁻¹) := by ring
      _ = X ^ 2 := by rw [hinv, mul_one]
  rw [hid, coeff_X_pow]
  split_ifs with h
  · subst h; norm_num [Nat.factorial]
  · simp

open OMA.S_oeis_a162171 in
lemma T_zero (i j : ℕ) (h : i < j) : A162169 (i + 1) (j + 1) = 0 := by
  unfold A162169
  split_ifs with h1 h2
  · simp [Nat.choose_eq_zero_of_lt h]
  · omega
  · rfl

open OMA.S_oeis_a162171 in
lemma T_diag (i : ℕ) : A162169 (i + 1) (i + 1) = 1 := by
  unfold A162169
  split_ifs with h1
  · have he : (i + 1 + (i + 1) - 1) / 2 = i := by omega
    rw [he, Nat.add_sub_cancel, Nat.choose_self]
    have : Even i := by rw [Nat.even_iff]; omega
    simp [this.neg_one_pow]
  all_goals simp_all

end A162171Proof

open A162171Proof OMA.S_oeis_a162171 PowerSeries Matrix in
theorem OMA.solution : type_of% @OMA.S_oeis_a162171.main := by
  intro n hn
  unfold a A162170
  rw [dif_pos (by omega)]
  set w : PowerSeries ℚ := (X : PowerSeries ℚ) ^ 2 *
    ((PowerSeries.cos ℚ)⁻¹ + PowerSeries.sin ℚ * (PowerSeries.cos ℚ)⁻¹) with hw
  let v : Fin (n + 2) → ℚ := fun j => ((j.val).factorial : ℚ) / 2 * coeff j.val w
  have hMv : M (n + 2) *ᵥ v = Pi.single ⟨2, by omega⟩ 1 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, M, v]
    rw [Fin.sum_univ_eq_sum_range (fun j => (A162169 (i.val + 1) (j + 1) : ℚ) *
      ((j.factorial : ℚ) / 2 * coeff j w)) (n + 2)]
    rw [← Finset.sum_subset (s₁ := Finset.range (i.val + 1))
      (by intro x hx; simp at hx ⊢; omega)
      (by
        intro x _ hx
        simp at hx
        rw [T_zero i.val x (by omega)]
        simp)]
    rw [hw, key i.val]
    by_cases h : i.val = 2
    · have : i = ⟨2, by omega⟩ := Fin.ext h
      rw [if_pos h, this, Pi.single_eq_same]
    · have : i ≠ ⟨2, by omega⟩ := fun h' => h (by rw [h'])
      rw [if_neg h, Pi.single_eq_of_ne this]
  have hdet : IsUnit (M (n + 2)).det := by
    rw [Matrix.det_of_isLowerTriangular]
    · simp only [M, T_diag]
      simp
    · intro i j hij
      simp only [M]
      rw [T_zero i.val j.val (by exact hij)]
      simp
  have hinv : (M (n + 2))⁻¹ *ᵥ (M (n + 2) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  rw [hMv, Matrix.mulVec_single_one] at hinv
  have hentry := congrFun hinv ⟨n + 2 - 1, by omega⟩
  simp only [Matrix.col_apply] at hentry
  rw [show (⟨3 - 1, by omega⟩ : Fin (n + 2)) = ⟨2, by omega⟩ from rfl, hentry]
  simp only [v]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : m + 1 + 2 - 1 = m + 2 := by omega
  simp only [e1, Nat.add_sub_cancel]
  rw [hw, coeff_X_pow_mul', if_pos (by omega), show m + 2 - 2 = m by omega]
  unfold A000111
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring
