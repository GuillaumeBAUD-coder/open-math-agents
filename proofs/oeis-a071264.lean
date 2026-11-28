import OMAStatements.S_oeis_a071264

open PowerSeries

private theorem coeff_ofNat_mul (n k : ℕ) [k.AtLeastTwo] (f : ℚ⟦X⟧) :
    coeff n ((ofNat(k) : ℚ⟦X⟧) * f) = ofNat(k) * coeff n f := by
  rw [← map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧), coeff_C_mul]

private theorem series_ofNat_ne_zero (k : ℕ) [k.AtLeastTwo] (hk : (ofNat(k) : ℚ) ≠ 0) :
    (ofNat(k) : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have hz := congrArg (constantCoeff (R := ℚ)) h
  rw [map_ofNat, map_zero] at hz
  exact hk hz

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private theorem coeff_X_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff k (X * derivative ℚ G) = (k : ℚ) * coeff k G := by
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_derivative, mul_comm]
    simp only [Nat.cast_add, Nat.cast_one]

/-- The coefficients of `sqrt (1 - 4 x)` satisfy a first order recurrence. -/
private theorem sqrt_coeff_rec (S : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X) (m : ℕ) :
    ((m : ℚ) + 1) * coeff (m + 1) S = (4 * (m : ℚ) - 2) * coeff m S := by
  have hd : 2 * S * derivative ℚ S = -4 := by
    have h := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hS
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at h
    linear_combination h
  have hode : derivative ℚ S - 4 * (X * derivative ℚ S) = -(2 * S) := by
    apply mul_left_cancel₀ (series_ofNat_ne_zero 2 (by norm_num))
    linear_combination S * hd - 2 * derivative ℚ S * hS
  have h := congrArg (coeff m) hode
  simp only [map_sub, map_neg, coeff_ofNat_mul, coeff_X_derivative, coeff_derivative] at h
  linear_combination h

theorem OMA.solution : type_of% @OMA.S_oeis_a071264.main := by
  intro S c G hS _ hc hG n hn
  have hSc : S = 1 - 2 * X * c := by linear_combination hc
  have hcat : c = 1 + X * c ^ 2 := by
    apply mul_left_cancel₀ (a := (4 : ℚ⟦X⟧) * X)
      (mul_ne_zero (series_ofNat_ne_zero 4 (by norm_num)) X_ne_zero)
    have h := hS
    rw [hSc] at h
    linear_combination -h
  have h2 : X ^ 1 * c ^ 2 = (1 : ℚ⟦X⟧) * c - (1 : ℚ⟦X⟧) := by
    linear_combination -hcat
  have h3 : X ^ 2 * c ^ 3 = (1 - X : ℚ⟦X⟧) * c - (1 : ℚ⟦X⟧) := by
    linear_combination (X * c) * h2 - (1 : ℚ⟦X⟧) * hcat
  have h4 : X ^ 3 * c ^ 4 = (1 - 2 * X : ℚ⟦X⟧) * c - (1 - X : ℚ⟦X⟧) := by
    linear_combination (X * c) * h3 - (1 - X : ℚ⟦X⟧) * hcat
  have h5 : X ^ 4 * c ^ 5 = (1 - 3 * X + X ^ 2 : ℚ⟦X⟧) * c - (1 - 2 * X : ℚ⟦X⟧) := by
    linear_combination (X * c) * h4 - (1 - 2 * X : ℚ⟦X⟧) * hcat
  have h6 : X ^ 5 * c ^ 6 = (1 - 4 * X + 3 * X ^ 2 : ℚ⟦X⟧) * c - (1 - 3 * X + X ^ 2 : ℚ⟦X⟧) := by
    linear_combination (X * c) * h5 - (1 - 3 * X + X ^ 2 : ℚ⟦X⟧) * hcat
  have h7 : X ^ 6 * c ^ 7 = (1 - 5 * X + 6 * X ^ 2 - X ^ 3 : ℚ⟦X⟧) * c - (1 - 4 * X + 3 * X ^ 2 : ℚ⟦X⟧) := by
    linear_combination (X * c) * h6 - (1 - 4 * X + 3 * X ^ 2 : ℚ⟦X⟧) * hcat
  have hmain : 2 * (X ^ 6 * G) = (1 - 7 * X + 14 * X ^ 2 - 6 * X ^ 3 - 3 * X ^ 4 : ℚ⟦X⟧) - ((X ^ 0 * S) - 5 * (X ^ 1 * S) + 6 * (X ^ 2 * S) - (X ^ 4 * S)) := by
    rw [hSc, hG]
    linear_combination (2 * X ^ 4) * h3 + (2 * X) * h7
  have ha : ∀ m : ℕ, 2 * coeff m G = -(coeff (m + 6) S - 5 * coeff (m + 5) S + 6 * coeff (m + 4) S - coeff (m + 2) S) := by
    intro m
    have e0 : coeff (m + 6) (X ^ 0 * S) = coeff (m + 6) S := by
      rw [show m + 6 = (m + 6) + 0 by omega, coeff_X_pow_mul]
    have e1 : coeff (m + 6) (X ^ 1 * S) = coeff (m + 5) S := by
      rw [show m + 6 = (m + 5) + 1 by omega, coeff_X_pow_mul]
    have e2 : coeff (m + 6) (X ^ 2 * S) = coeff (m + 4) S := by
      rw [show m + 6 = (m + 4) + 2 by omega, coeff_X_pow_mul]
    have e4 : coeff (m + 6) (X ^ 4 * S) = coeff (m + 2) S := by
      rw [show m + 6 = (m + 2) + 4 by omega, coeff_X_pow_mul]
    have eG : coeff (m + 6) (X ^ 6 * G) = coeff m G := coeff_X_pow_mul _ _ _
    have h := congrArg (coeff (m + 6)) hmain
    have hP : coeff (m + 6) (1 - 7 * X + 14 * X ^ 2 - 6 * X ^ 3 - 3 * X ^ 4 : ℚ⟦X⟧) = 0 := by
      simp (disch := omega) only [map_add, map_sub, map_neg, coeff_ofNat_mul, coeff_one,
        coeff_X, coeff_X_pow, if_neg, mul_zero, add_zero, sub_zero, neg_zero]
    simp only [map_add, map_sub, map_neg, coeff_ofNat_mul, hP, eG, e0, e1, e2, e4] at h
    linear_combination h
  have hs := sqrt_coeff_rec S hS
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have r2 : coeff (k + 3) S =
      (4 * ((k : ℚ) + 2) - 2) / ((k : ℚ) + 3) * coeff (k + 2) S := by
    have h := hs (k + 2)
    rw [show k + 2 + 1 = k + 3 by omega] at h
    push_cast at h
    have hne : (k : ℚ) + 3 ≠ 0 := by positivity
    rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination h
  have r3 : coeff (k + 4) S =
      (4 * ((k : ℚ) + 3) - 2) / ((k : ℚ) + 4) * coeff (k + 3) S := by
    have h := hs (k + 3)
    rw [show k + 3 + 1 = k + 4 by omega] at h
    push_cast at h
    have hne : (k : ℚ) + 4 ≠ 0 := by positivity
    rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination h
  have r4 : coeff (k + 5) S =
      (4 * ((k : ℚ) + 4) - 2) / ((k : ℚ) + 5) * coeff (k + 4) S := by
    have h := hs (k + 4)
    rw [show k + 4 + 1 = k + 5 by omega] at h
    push_cast at h
    have hne : (k : ℚ) + 5 ≠ 0 := by positivity
    rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination h
  have r5 : coeff (k + 6) S =
      (4 * ((k : ℚ) + 5) - 2) / ((k : ℚ) + 6) * coeff (k + 5) S := by
    have h := hs (k + 5)
    rw [show k + 5 + 1 = k + 6 by omega] at h
    push_cast at h
    have hne : (k : ℚ) + 6 ≠ 0 := by positivity
    rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination h
  have r6 : coeff (k + 7) S =
      (4 * ((k : ℚ) + 6) - 2) / ((k : ℚ) + 7) * coeff (k + 6) S := by
    have h := hs (k + 6)
    rw [show k + 6 + 1 = k + 7 by omega] at h
    push_cast at h
    have hne : (k : ℚ) + 7 ≠ 0 := by positivity
    rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination h
  have r7 : coeff (k + 8) S =
      (4 * ((k : ℚ) + 7) - 2) / ((k : ℚ) + 8) * coeff (k + 7) S := by
    have h := hs (k + 7)
    rw [show k + 7 + 1 = k + 8 by omega] at h
    push_cast at h
    have hne : (k : ℚ) + 8 ≠ 0 := by positivity
    rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination h
  have A2 : coeff (k + 2) G = -(coeff (k + 8) S - 5 * coeff (k + 7) S + 6 * coeff (k + 6) S - coeff (k + 4) S) / 2 := by
    have h := ha (k + 2)
    simp only [add_assoc, Nat.reduceAdd, Nat.add_zero] at h ⊢
    linear_combination h / 2
  have A1 : coeff (k + 1) G = -(coeff (k + 7) S - 5 * coeff (k + 6) S + 6 * coeff (k + 5) S - coeff (k + 3) S) / 2 := by
    have h := ha (k + 1)
    simp only [add_assoc, Nat.reduceAdd, Nat.add_zero] at h ⊢
    linear_combination h / 2
  have A0 : coeff (k + 0) G = -(coeff (k + 6) S - 5 * coeff (k + 5) S + 6 * coeff (k + 4) S - coeff (k + 2) S) / 2 := by
    have h := ha (k + 0)
    simp only [add_assoc, Nat.reduceAdd, Nat.add_zero] at h ⊢
    linear_combination h / 2
  simp only [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k + 0 by omega]
  rw [A2, A1, A0]
  rw [r7, r6, r5, r4, r3, r2]
  push_cast
  have d3 : (k : ℚ) + 3 ≠ 0 := by positivity
  have d4 : (k : ℚ) + 4 ≠ 0 := by positivity
  have d5 : (k : ℚ) + 5 ≠ 0 := by positivity
  have d6 : (k : ℚ) + 6 ≠ 0 := by positivity
  have d7 : (k : ℚ) + 7 ≠ 0 := by positivity
  have d8 : (k : ℚ) + 8 ≠ 0 := by positivity
  field_simp
  ring
