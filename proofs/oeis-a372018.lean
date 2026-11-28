import OMAStatements.S_oeis_a372018
import Mathlib

/-!
Proof idea: u = X * A satisfies u^2 (1 - u) = X^2 (1 + 3 u), an equation in X^2 only, so
v = u(-X) is a second root of w^3 - w^2 + 3 X^2 w + X^2 and E = 1 - u - v is the third (Vieta).
E is even, E = F(X^2), and F and 1 - 4 T both solve w^3 - w^2 + 3 X w + X = 0 with constant
term 1, hence agree. Comparing coefficients gives a(2n+1) = 2 [X^(n+1)] T.
-/

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a372018.main := by
  intro A T hA0 hA hT0 hT n
  set u : ℚ⟦X⟧ := X * A with hu_def
  have hu : u ^ 2 * (1 - u) = X ^ 2 * (1 + 3 * u) := by
    rw [hu_def]; linear_combination X ^ 2 * hA
  set v : ℚ⟦X⟧ := rescale (-1 : ℚ) u with hv_def
  have hv : v ^ 2 * (1 - v) = X ^ 2 * (1 + 3 * v) := by
    have h := congrArg (rescale (-1 : ℚ)) hu
    simp only [map_mul, map_pow, map_sub, map_one, map_add, rescale_neg_one_X, map_ofNat] at h
    rw [← hv_def] at h
    linear_combination h
  have hu1 : coeff 1 u = 1 := by
    rw [hu_def, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, hA0]
  have hv1 : coeff 1 v = -1 := by
    rw [hv_def, coeff_rescale, hu1]; norm_num
  have hne : u - v ≠ 0 := by
    intro h
    have := congrArg (coeff 1) h
    rw [map_sub, hu1, hv1, map_zero] at this
    norm_num at this
  have hq : u ^ 2 + u * v + v ^ 2 - u - v + 3 * X ^ 2 = 0 := by
    have h : (u - v) * (u ^ 2 + u * v + v ^ 2 - u - v + 3 * X ^ 2) = 0 := by
      linear_combination hv - hu
    exact (mul_eq_zero.mp h).resolve_left hne
  set E : ℚ⟦X⟧ := 1 - u - v with hE_def
  have hE : E ^ 3 - E ^ 2 + 3 * X ^ 2 * E + X ^ 2 = 0 := by
    rw [hE_def]; linear_combination (1 - 2 * u - v) * hq - hu
  have hEodd : ∀ m : ℕ, m % 2 = 1 → coeff m E = 0 := by
    intro m hm
    have hodd : Odd m := Nat.odd_iff.mpr hm
    have hm0 : m ≠ 0 := by omega
    rw [hE_def, map_sub, map_sub, coeff_one, if_neg hm0, hv_def, coeff_rescale, hodd.neg_one_pow]
    ring
  set F : ℚ⟦X⟧ := mk (fun k => coeff (2 * k) E) with hF_def
  have hEF : expand 2 two_ne_zero F = E := by
    ext m
    rw [coeff_expand]
    split_ifs with h
    · obtain ⟨k, rfl⟩ := h
      rw [hF_def, coeff_mk, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
    · exact (hEodd m (Nat.two_dvd_ne_zero.mp h)).symm
  have hF : F ^ 3 - F ^ 2 + 3 * X * F + X = 0 := by
    have h : expand 2 two_ne_zero (F ^ 3 - F ^ 2 + 3 * X * F + X) = 0 := by
      simp only [map_add, map_sub, map_mul, map_pow, expand_X, hEF, map_ofNat]
      linear_combination hE
    ext k
    have h2 := congrArg (coeff (2 * k)) h
    rw [coeff_expand_mul, map_zero] at h2
    rw [h2, map_zero]
  set W : ℚ⟦X⟧ := 1 - 4 * T with hW_def
  have hW : W ^ 3 - W ^ 2 + 3 * X * W + X = 0 := by
    rw [hW_def]; linear_combination (-4) * hT
  have hu0 : constantCoeff u = 0 := by
    rw [hu_def, map_mul, constantCoeff_X, zero_mul]
  have hv0 : constantCoeff v = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hv_def, coeff_rescale, coeff_zero_eq_constantCoeff_apply,
      hu0, mul_zero]
  have hF0 : constantCoeff F = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hF_def, coeff_mk, mul_zero,
      coeff_zero_eq_constantCoeff_apply, hE_def, map_sub, map_sub, map_one, hu0, hv0]
    ring
  have hW0 : constantCoeff W = 1 := by
    rw [hW_def, map_sub, map_one, map_mul, ← coeff_zero_eq_constantCoeff_apply T, hT0, mul_zero, sub_zero]
  have hFW : F = W := by
    have h : (F - W) * (F ^ 2 + F * W + W ^ 2 - F - W + 3 * X) = 0 := by
      linear_combination hF - hW
    have hne2 : F ^ 2 + F * W + W ^ 2 - F - W + 3 * X ≠ 0 := by
      intro h0
      have := congrArg constantCoeff h0
      simp only [map_add, map_sub, map_mul, map_pow, hF0, hW0, constantCoeff_X, map_ofNat,
        map_zero] at this
      norm_num at this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hne2)
  have hl : coeff (n + 1) F = -2 * coeff (2 * n + 1) A := by
    have hpow : ((-1 : ℚ)) ^ (2 * n + 1 + 1) = 1 := by
      rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul]; norm_num
    rw [hF_def, coeff_mk, hE_def, map_sub, map_sub, coeff_one, if_neg (by omega), hv_def,
      coeff_rescale, show 2 * (n + 1) = (2 * n + 1) + 1 by ring, hpow, hu_def, coeff_succ_X_mul]
    ring
  have hr : coeff (n + 1) W = -4 * coeff (n + 1) T := by
    rw [hW_def, map_sub, coeff_one, if_neg (Nat.succ_ne_zero n),
      show (4 : ℚ⟦X⟧) = C (4 : ℚ) from (map_ofNat C 4).symm, coeff_C_mul]
    ring
  have h1 := congrArg (coeff (n + 1)) hFW
  rw [hl, hr] at h1
  linarith
