import OMAStatements.S_oeis_a089324

open PowerSeries

namespace OMA.PathSeries

open OMA.S_oeis_a089324

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

private noncomputable def A : PowerSeries ℚ :=
  (-1 + 2 * X - X ^ 2 + S) * (2 - 6 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹

private theorem differential :
    (X - 3 * X ^ 2 - 5 * X ^ 3 + 18 * X ^ 4 - 5 * X ^ 5 - 3 * X ^ 6 + X ^ 7) *
        derivative ℚ A + (-3 * X + 8 * X ^ 2 - 8 * X ^ 4 + 3 * X ^ 5) * A =
      X - 4 * X ^ 2 + 4 * X ^ 4 - X ^ 5 := by
  let Q : PowerSeries ℚ := 2 - 6 * X + 2 * X ^ 2
  let P : PowerSeries ℚ := -1 + 2 * X - X ^ 2
  have c2 : constantCoeff (2 : PowerSeries ℚ) = (2 : ℚ) :=
    map_natCast (constantCoeff (R := ℚ)) 2
  have c4 : constantCoeff (4 : PowerSeries ℚ) = (4 : ℚ) :=
    map_natCast (constantCoeff (R := ℚ)) 4
  have four_ne : (4 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg (constantCoeff (R := ℚ)) h
    rw [c4, map_zero] at h'
    norm_num at h'
  have hQ : constantCoeff Q ≠ 0 := by
    norm_num [Q, c2]
  have hQA : Q * A = P + S := by
    change Q * ((P + S) * Q⁻¹) = P + S
    rw [mul_left_comm, PowerSeries.mul_inv_cancel Q hQ, mul_one]
  have diffS : 2 * S * derivative ℚ S = derivative ℚ R := by
    have h := congrArg (derivative ℚ) square_root
    simpa only [derivative_pow, Nat.reduceSub, pow_one, Nat.cast_ofNat] using h
  have diffRS : 2 * R * derivative ℚ S = derivative ℚ R * S := by
    calc
      _ = S * (2 * S * derivative ℚ S) := by rw [← square_root]; ring
      _ = _ := by rw [diffS]; ring
  have derivQA : Q * derivative ℚ A + derivative ℚ Q * A = derivative ℚ P + derivative ℚ S := by
    have h := congrArg (derivative ℚ) hQA
    simpa only [Derivation.leibniz, smul_eq_mul, map_add, mul_comm (derivative ℚ Q) A] using h
  have d2 : derivative ℚ (2 : PowerSeries ℚ) = 0 := (derivative ℚ).map_natCast 2
  have d6 : derivative ℚ (6 : PowerSeries ℚ) = 0 := (derivative ℚ).map_natCast 6
  have derivQ : derivative ℚ Q = -6 + 4 * X := by
    simp [Q, Derivation.leibniz, smul_eq_mul, d2, d6] <;> ring
  have derivP : derivative ℚ P = 2 - 2 * X := by
    simp [P, Derivation.leibniz, smul_eq_mul, d2]
  have derivR : derivative ℚ R = -12 * X + 4 * X ^ 3 := by
    simp [R, Derivation.leibniz, smul_eq_mul, d6] <;> ring
  have hcore :
      2 * R * (Q * derivative ℚ A + derivative ℚ Q * A) - derivative ℚ R * (Q * A) =
        2 * R * derivative ℚ P - derivative ℚ R * P := by
    rw [derivQA, hQA]
    linear_combination diffRS
  rw [derivQ, derivP, derivR] at hcore
  dsimp only [Q, P, R] at hcore
  apply mul_left_cancel₀ (a := (4 : PowerSeries ℚ)) four_ne
  linear_combination X * hcore

private theorem coeff_shift (n j : ℕ) (hj : j ≤ n) (r : ℚ) (p : PowerSeries ℚ) :
    coeff n (C r * X ^ j * p) = r * coeff (n - j) p := by
  rw [mul_assoc, coeff_C_mul]
  have h := coeff_X_pow_mul p j (n - j)
  rw [Nat.sub_add_cancel hj] at h
  rw [h]

private theorem recurrence (n : ℕ) (hn : 6 ≤ n) :
    ((n : ℚ) + 1) * a n + (-3 * (n : ℚ) - 3) * a (n - 1) + (-5 * (n : ℚ) + 13) * a (n - 2)
      + (18 * (n : ℚ) - 36) * a (n - 3) + (-5 * (n : ℚ) + 7) * a (n - 4)
      + (-3 * (n : ℚ) + 15) * a (n - 5) + ((n : ℚ) - 5) * a (n - 6) = 0 := by
  have hs :
      C 1 * X ^ 1 * derivative ℚ A + C (-3) * X ^ 2 * derivative ℚ A +
        C (-5) * X ^ 3 * derivative ℚ A + C 18 * X ^ 4 * derivative ℚ A +
        C (-5) * X ^ 5 * derivative ℚ A + C (-3) * X ^ 6 * derivative ℚ A +
        C 1 * X ^ 7 * derivative ℚ A +
        C (-3) * X ^ 1 * A + C 8 * X ^ 2 * A + C (-8) * X ^ 4 * A + C 3 * X ^ 5 * A =
      X - C 4 * X ^ 2 + C 4 * X ^ 4 - X ^ 5 := by
    have h := differential
    simp only [map_neg, map_one, map_ofNat, pow_one]
    linear_combination h
  have dc (j : ℕ) (hj : j ≤ n) (r : ℚ) :
      coeff (n + 1) (C r * X ^ (j + 1) * derivative ℚ A) =
        r * (a (n - j) * ((n : ℚ) - (j : ℚ) + 1)) := by
    rw [coeff_shift _ _ (by omega), show n + 1 - (j + 1) = n - j by omega,
      coeff_derivative, Nat.cast_sub hj]
    rfl
  have oc (j : ℕ) (hj : j ≤ n) (r : ℚ) :
      coeff (n + 1) (C r * X ^ j * A) = r * a (n - j) := by
    rw [coeff_shift _ _ (by omega), show n + 1 - j = (n - j) + 1 by omega]
    rfl
  have hz : coeff (n + 1) (X - C 4 * X ^ 2 + C 4 * X ^ 4 - X ^ 5 : PowerSeries ℚ) = 0 := by
    simp only [map_sub, map_add, coeff_X, coeff_X_pow, coeff_C_mul_X_pow,
      if_neg (by omega : n + 1 ≠ 1), if_neg (by omega : n + 1 ≠ 2),
      if_neg (by omega : n + 1 ≠ 4), if_neg (by omega : n + 1 ≠ 5), sub_zero, zero_add]
  have h := congrArg (coeff (n + 1)) hs
  rw [hz] at h
  simp only [map_add, dc 0 (Nat.zero_le n), dc 1 (by omega), dc 2 (by omega),
    dc 3 (by omega), dc 4 (by omega), dc 5 (by omega), dc 6 hn, oc 1 (by omega),
    oc 2 (by omega), oc 4 (by omega), oc 5 (by omega), Nat.sub_zero, Nat.cast_zero,
    Nat.cast_succ, Nat.cast_ofNat] at h
  linear_combination h

end OMA.PathSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a089324.main := OMA.PathSeries.recurrence