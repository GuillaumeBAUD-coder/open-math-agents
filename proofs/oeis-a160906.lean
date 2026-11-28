import OMAStatements.S_oeis_a160906

open PowerSeries

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

private theorem coeff_X_sq_derivative2 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff k (X ^ 2 * derivative ℚ (derivative ℚ G)) =
      (k : ℚ) * ((k : ℚ) - 1) * coeff k G := by
  match k with
  | 0 =>
    rw [pow_two, mul_assoc]
    simp
  | 1 =>
    rw [pow_two, mul_assoc, coeff_succ_X_mul]
    simp
  | k + 2 =>
    rw [pow_two, mul_assoc, coeff_succ_X_mul, coeff_succ_X_mul,
      coeff_derivative, coeff_derivative]
    push_cast
    ring

private theorem coeff_X_cube_derivative3 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff k (X ^ 3 * derivative ℚ (derivative ℚ (derivative ℚ G))) =
      (k : ℚ) * ((k : ℚ) - 1) * ((k : ℚ) - 2) * coeff k G := by
  have h3 : (X : ℚ⟦X⟧) ^ 3 = X * (X * X) := by ring
  rw [h3, mul_assoc, mul_assoc]
  match k with
  | 0 => simp
  | 1 => rw [coeff_succ_X_mul]; simp
  | 2 => rw [coeff_succ_X_mul, coeff_succ_X_mul]; simp
  | k + 3 =>
    rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_succ_X_mul,
      coeff_derivative, coeff_derivative, coeff_derivative]
    push_cast
    ring

private theorem generating_function_ode (T G : ℚ⟦X⟧)
    (hT : T = 1 + X * T ^ 3)
    (hG : G * ((2 - T) * (3 - 2 * T)) = T ^ 2) :
    C 2112 * (X * G) + C 2 * G +
      C 11328 * (X * (X * derivative ℚ G)) - C 842 * (X * derivative ℚ G) +
      C 2 * derivative ℚ G +
      C 7776 * (X * (X ^ 2 * derivative ℚ (derivative ℚ G))) -
      C 1319 * (X ^ 2 * derivative ℚ (derivative ℚ G)) +
      C 34 * (X * derivative ℚ (derivative ℚ G)) +
      C 1080 * (X * (X ^ 3 * derivative ℚ (derivative ℚ (derivative ℚ G)))) -
      C 295 * (X ^ 3 * derivative ℚ (derivative ℚ (derivative ℚ G))) +
      C 20 * (X ^ 2 * derivative ℚ (derivative ℚ (derivative ℚ G))) = C 12 := by
  have hT0 : constantCoeff T = 1 := by
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) hT
    simpa using hc
  have hDne : T ^ 12 * (2 - T) ^ 4 * (3 - 2 * T) ^ 7 ≠ 0 := by
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    simp [hT0, map_ofNat] at hc
    norm_num at hc
  have hXT : X * T ^ 3 = T - 1 := by linear_combination -hT
  have hTd : (3 - 2 * T) * derivative ℚ T = T ^ 4 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hT
    simp [Derivation.leibniz, smul_eq_mul] at hd
    linear_combination T * hd - 3 * derivative ℚ T * hT
  have hG1 : (2 - T) ^ 2 * (3 - 2 * T) ^ 3 * derivative ℚ G = 12 * T ^ 5 - 7 * T ^ 6 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hG
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination
      (2 - T) * (3 - 2 * T) ^ 2 * hd +
        (7 - 4 * T) * (3 - 2 * T) * derivative ℚ T * hG +
        ((7 - 4 * T) * T ^ 2 + 2 * T * (2 - T) * (3 - 2 * T)) * hTd
  have hG2 : (2 - T) ^ 3 * (3 - 2 * T) ^ 5 * derivative ℚ (derivative ℚ G) =
      360 * T ^ 8 - 456 * T ^ 9 + 168 * T ^ 10 - 14 * T ^ 11 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hG1
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination
      (2 - T) * (3 - 2 * T) ^ 2 * hd +
        (18 - 10 * T) * (3 - 2 * T) * derivative ℚ T * hG1 +
        ((18 - 10 * T) * (12 * T ^ 5 - 7 * T ^ 6) +
          (2 - T) * (3 - 2 * T) * (60 * T ^ 4 - 42 * T ^ 5)) * hTd
  have hG3 : (2 - T) ^ 4 * (3 - 2 * T) ^ 7 * derivative ℚ (derivative ℚ (derivative ℚ G)) =
      17280 * T ^ 11 - 34344 * T ^ 12 + 25584 * T ^ 13 -
      8724 * T ^ 14 + 1344 * T ^ 15 - 84 * T ^ 16 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hG2
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination
      (2 - T) * (3 - 2 * T) ^ 2 * hd +
        (29 - 16 * T) * (3 - 2 * T) * derivative ℚ T * hG2 +
        ((29 - 16 * T) * (360 * T ^ 8 - 456 * T ^ 9 + 168 * T ^ 10 - 14 * T ^ 11) +
          (2 - T) * (3 - 2 * T) * (2880 * T ^ 7 - 4104 * T ^ 8 + 1680 * T ^ 9 - 154 * T ^ 10)) * hTd
  rw [map_ofNat C 2112, map_ofNat C 2, map_ofNat C 11328, map_ofNat C 842,
    map_ofNat C 7776, map_ofNat C 1319, map_ofNat C 34, map_ofNat C 1080,
    map_ofNat C 295, map_ofNat C 20, map_ofNat C 12]
  apply mul_left_cancel₀ hDne
  have hP0 : T ^ 12 * (2 - T) ^ 4 * (3 - 2 * T) ^ 7 * (2112 * (X * G) + 2 * G) =
      (2112 * (T - 1) * T ^ 9 + 2 * T ^ 12) * (2 - T) ^ 3 * (3 - 2 * T) ^ 6 * T ^ 2 := by
    calc T ^ 12 * (2 - T) ^ 4 * (3 - 2 * T) ^ 7 * (2112 * (X * G) + 2 * G)
        = (2112 * (X * T ^ 3) * T ^ 9 + 2 * T ^ 12) * (2 - T) ^ 3 * (3 - 2 * T) ^ 6 *
            (G * ((2 - T) * (3 - 2 * T))) := by ring
      _ = _ := by rw [hXT, hG]
  have hP1 : T ^ 12 * (2 - T) ^ 4 * (3 - 2 * T) ^ 7 *
      (11328 * (X * (X * derivative ℚ G)) - 842 * (X * derivative ℚ G) + 2 * derivative ℚ G) =
      (11328 * (T - 1) ^ 2 * T ^ 6 - 842 * (T - 1) * T ^ 9 + 2 * T ^ 12) *
        (2 - T) ^ 2 * (3 - 2 * T) ^ 4 * (12 * T ^ 5 - 7 * T ^ 6) := by
    calc T ^ 12 * (2 - T) ^ 4 * (3 - 2 * T) ^ 7 *
          (11328 * (X * (X * derivative ℚ G)) - 842 * (X * derivative ℚ G) + 2 * derivative ℚ G)
        = (11328 * (X * T ^ 3) ^ 2 * T ^ 6 - 842 * (X * T ^ 3) * T ^ 9 + 2 * T ^ 12) *
            (2 - T) ^ 2 * (3 - 2 * T) ^ 4 * ((2 - T) ^ 2 * (3 - 2 * T) ^ 3 * derivative ℚ G) := by ring
      _ = _ := by rw [hXT, hG1]
  have hP2 : T ^ 12 * (2 - T) ^ 4 * (3 - 2 * T) ^ 7 *
      (7776 * (X * (X ^ 2 * derivative ℚ (derivative ℚ G))) -
        1319 * (X ^ 2 * derivative ℚ (derivative ℚ G)) +
        34 * (X * derivative ℚ (derivative ℚ G))) =
      (7776 * (T - 1) ^ 3 * T ^ 3 - 1319 * (T - 1) ^ 2 * T ^ 6 + 34 * (T - 1) * T ^ 9) *
        (2 - T) * (3 - 2 * T) ^ 2 * (360 * T ^ 8 - 456 * T ^ 9 + 168 * T ^ 10 - 14 * T ^ 11) := by
    calc T ^ 12 * (2 - T) ^ 4 * (3 - 2 * T) ^ 7 *
          (7776 * (X * (X ^ 2 * derivative ℚ (derivative ℚ G))) -
            1319 * (X ^ 2 * derivative ℚ (derivative ℚ G)) +
            34 * (X * derivative ℚ (derivative ℚ G)))
        = (7776 * (X * T ^ 3) ^ 3 * T ^ 3 - 1319 * (X * T ^ 3) ^ 2 * T ^ 6 +
            34 * (X * T ^ 3) * T ^ 9) * (2 - T) * (3 - 2 * T) ^ 2 *
            ((2 - T) ^ 3 * (3 - 2 * T) ^ 5 * derivative ℚ (derivative ℚ G)) := by ring
      _ = _ := by rw [hXT, hG2]
  have hP3 : T ^ 12 * (2 - T) ^ 4 * (3 - 2 * T) ^ 7 *
      (1080 * (X * (X ^ 3 * derivative ℚ (derivative ℚ (derivative ℚ G)))) -
        295 * (X ^ 3 * derivative ℚ (derivative ℚ (derivative ℚ G))) +
        20 * (X ^ 2 * derivative ℚ (derivative ℚ (derivative ℚ G)))) =
      (1080 * (T - 1) ^ 4 - 295 * (T - 1) ^ 3 * T ^ 3 + 20 * (T - 1) ^ 2 * T ^ 6) *
        (17280 * T ^ 11 - 34344 * T ^ 12 + 25584 * T ^ 13 -
          8724 * T ^ 14 + 1344 * T ^ 15 - 84 * T ^ 16) := by
    calc T ^ 12 * (2 - T) ^ 4 * (3 - 2 * T) ^ 7 *
          (1080 * (X * (X ^ 3 * derivative ℚ (derivative ℚ (derivative ℚ G)))) -
            295 * (X ^ 3 * derivative ℚ (derivative ℚ (derivative ℚ G))) +
            20 * (X ^ 2 * derivative ℚ (derivative ℚ (derivative ℚ G))))
        = (1080 * (X * T ^ 3) ^ 4 - 295 * (X * T ^ 3) ^ 3 * T ^ 3 +
            20 * (X * T ^ 3) ^ 2 * T ^ 6) *
            ((2 - T) ^ 4 * (3 - 2 * T) ^ 7 * derivative ℚ (derivative ℚ (derivative ℚ G))) := by ring
      _ = _ := by rw [hXT, hG3]
  linear_combination hP0 + hP1 + hP2 + hP3

theorem OMA.solution : type_of% @OMA.S_oeis_a160906.main := by
  intro T G hT hG _ n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hc := congrArg (coeff (k + 1)) (generating_function_ode T G hT hG)
  simp only [map_add, map_sub, coeff_C_mul, coeff_C, Nat.succ_ne_zero, ite_false,
    coeff_succ_X_mul, coeff_X_derivative, coeff_X_sq_derivative2,
    coeff_X_cube_derivative3, coeff_derivative] at hc
  simp only [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  push_cast at hc ⊢
  linear_combination hc
