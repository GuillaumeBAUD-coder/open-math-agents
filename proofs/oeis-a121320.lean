import OMAStatements.S_oeis_a121320

open PowerSeries

namespace OMA.TreeSeries

open OMA.S_oeis_a121320

private theorem square_root : S ^ 2 = R := by
  have hsub : PowerSeries.HasSubst (R - 1) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    simp [R]
  let g : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ := PowerSeries.substAlgHom hsub
  let b := PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)
  have hb : b ^ 2 = 1 + X := by
    rw [pow_two]
    change PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) * PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) = _
    rw [← PowerSeries.binomialSeries_add]
    rw [show (1 / 2 : ℚ) + 1 / 2 = ((1 : ℕ) : ℚ) by norm_num,
      PowerSeries.binomialSeries_nat, pow_one]
  have gx : g X = R - 1 := by
    simp only [g, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hsub]
  unfold S
  rw [← PowerSeries.coe_substAlgHom hsub]
  change (g b) ^ 2 = R
  rw [← map_pow, hb, map_add, map_one, gx]
  ring

private noncomputable def U : PowerSeries ℚ := 1 - X - X ^ 2

private noncomputable def A : PowerSeries ℚ :=
  (X ^ 2 - 4 * X ^ 3 + (X ^ 2) * S)
    * (2 - 10 * X + 6 * X ^ 2 + 8 * X ^ 3 : PowerSeries ℚ)⁻¹

private theorem differential :
    (-X + 5 * X ^ 2 - 3 * X ^ 3 - 4 * X ^ 4) * derivative ℚ A +
      (2 - 7 * X + 2 * X ^ 2 - 2 * X ^ 3) * A = X ^ 3 := by
  let D : PowerSeries ℚ := 2 - 10 * X + 6 * X ^ 2 + 8 * X ^ 3
  let N : PowerSeries ℚ := X ^ 2 * (R + S)
  have c2 : constantCoeff (2 : PowerSeries ℚ) = (2 : ℚ) :=
    map_natCast (constantCoeff (R := ℚ)) 2
  have two_ne : (2 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg (constantCoeff (R := ℚ)) h
    rw [c2, map_zero] at h'
    norm_num at h'
  have hD : constantCoeff D ≠ 0 := by
    norm_num [D, c2]
  have hDA : D * A = N := by
    change D * ((X ^ 2 - 4 * X ^ 3 + X ^ 2 * S) * D⁻¹) = N
    rw [mul_left_comm, PowerSeries.mul_inv_cancel D hD, mul_one]
    dsimp only [N, R]
    ring
  have derivR : derivative ℚ R = -4 := by
    have d4 : derivative ℚ (4 : PowerSeries ℚ) = 0 := (derivative ℚ).map_natCast 4
    simp [R, Derivation.leibniz, smul_eq_mul, d4]
  have derivU : derivative ℚ U = -1 - 2 * X := by
    simp [U]
  have diffS : 2 * S * derivative ℚ S = -4 := by
    have h := congrArg (derivative ℚ) square_root
    simpa only [derivative_pow, derivR, Nat.reduceSub, pow_one, Nat.cast_ofNat] using h
  have diffRS : R * derivative ℚ S = -2 * S := by
    apply mul_left_cancel₀ (a := (2 : PowerSeries ℚ)) two_ne
    calc
      _ = S * (2 * S * derivative ℚ S) := by rw [← square_root]; ring
      _ = _ := by rw [diffS]; ring
  have derivN : derivative ℚ N =
      2 * X * (R + S) + X ^ 2 * (-4 + derivative ℚ S) := by
    simp only [N, Derivation.leibniz, smul_eq_mul, map_add, derivR, derivative_pow,
      derivative_X, Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one]
    ring
  have odeN : X * R * derivative ℚ N = (2 - 10 * X) * N - 2 * X ^ 3 * R := by
    rw [derivN]
    dsimp only [N]
    unfold R at diffRS ⊢
    linear_combination X ^ 3 * diffRS
  have derivDA : D * derivative ℚ A + derivative ℚ D * A = derivative ℚ N := by
    have h := congrArg (derivative ℚ) hDA
    simpa only [Derivation.leibniz, smul_eq_mul, mul_comm (derivative ℚ D) A] using h
  have factorD : D = 2 * R * U := by
    dsimp [D, R, U]
    ring
  have derivD : derivative ℚ D = 2 * (R * derivative ℚ U + derivative ℚ R * U) := by
    rw [factorD]
    have d2 : derivative ℚ (2 : PowerSeries ℚ) = 0 := (derivative ℚ).map_natCast 2
    simp only [Derivation.leibniz, smul_eq_mul, d2, mul_zero, add_zero]
    ring
  have hcore :
      X * R * (D * derivative ℚ A + derivative ℚ D * A) =
        (2 - 10 * X) * (D * A) - 2 * X ^ 3 * R := by
    rw [derivDA, hDA]
    exact odeN
  rw [derivD, factorD, derivU, derivR] at hcore
  have hR : R ≠ 0 := by
    intro h
    have := congrArg (constantCoeff (R := ℚ)) h
    simp [R] at this
  apply mul_left_cancel₀ (a := 2 * R) (mul_ne_zero two_ne hR)
  unfold R U at hcore
  unfold R
  linear_combination -hcore

private theorem coeff_shift (n j : ℕ) (hj : j ≤ n) (r : ℚ) (p : PowerSeries ℚ) :
    coeff n (C r * X ^ j * p) = r * coeff (n - j) p := by
  rw [mul_assoc, coeff_C_mul]
  have h := coeff_X_pow_mul p j (n - j)
  rw [Nat.sub_add_cancel hj] at h
  rw [h]

private theorem recurrence (n : ℕ) (hn : 4 ≤ n) :
    (-(n : ℚ) + 2) * a n + (5 * (n : ℚ) - 12) * a (n - 1)
      + (-3 * (n : ℚ) + 8) * a (n - 2) + (-4 * (n : ℚ) + 10) * a (n - 3) = 0 := by
  have hs :
      C (-1) * X ^ 1 * derivative ℚ A + C 5 * X ^ 2 * derivative ℚ A +
        C (-3) * X ^ 3 * derivative ℚ A + C (-4) * X ^ 4 * derivative ℚ A +
        C 2 * X ^ 0 * A + C (-7) * X ^ 1 * A +
        C 2 * X ^ 2 * A + C (-2) * X ^ 3 * A = X ^ 3 := by
    have h := differential
    simp only [map_neg, map_one, map_ofNat, pow_one, pow_zero]
    linear_combination h
  have h := congrArg (coeff n) hs
  have s1 : n - 1 + 1 = n := by omega
  have s2 : n - 2 + 1 = n - 1 := by omega
  have s3 : n - 3 + 1 = n - 2 := by omega
  have s4 : n - 4 + 1 = n - 3 := by omega
  have ha (k : ℕ) : coeff k A = a k := rfl
  simp only [map_add, coeff_shift n 0 (Nat.zero_le n), coeff_shift n 1 (by omega),
    coeff_shift n 2 (by omega), coeff_shift n 3 (by omega), coeff_shift n 4 hn, coeff_derivative,
    s1, s2, s3, s4, Nat.sub_zero, ha, coeff_X_pow, if_neg (by omega : n ≠ 3)] at h
  push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
    Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub hn] at h
  linear_combination h

end OMA.TreeSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a121320.main := OMA.TreeSeries.recurrence