import OMAStatements.S_oeis_a172062

open PowerSeries

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private theorem nz_ofNat (m : ℕ) [m.AtLeastTwo] : (no_index (OfNat.ofNat m : ℚ⟦X⟧)) ≠ 0 := by
  rw [← map_ofNat C m]
  intro h
  have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
  change constantCoeff (C (m : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
  simp at hc
  have : 2 ≤ m := Nat.AtLeastTwo.prop
  omega

private theorem nz_X : (X : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have hc := congrArg (coeff 1) h
  simp at hc

private theorem nz_one_sub_4X : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
  simp at hc

private theorem nz_two_add_X : (2 + X : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
  simp at hc
  rw [← map_ofNat C 2] at hc
  change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
  simp at hc

private theorem generating_function_ode (S c G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X)
    (hc : 2 * X * c = 1 - S)
    (hG : G * (3 * S - 1 + 4 * X) = 2 * c ^ 5) :
    C 6 * (X ^ 2 * derivative ℚ (derivative ℚ (derivative ℚ G))) -
      C 21 * (X ^ 3 * derivative ℚ (derivative ℚ (derivative ℚ G))) -
      C 12 * (X ^ 4 * derivative ℚ (derivative ℚ (derivative ℚ G))) +
      C 62 * (X * derivative ℚ (derivative ℚ G)) -
      C 268 * (X ^ 2 * derivative ℚ (derivative ℚ G)) -
      C 190 * (X ^ 3 * derivative ℚ (derivative ℚ G)) +
      C 120 * derivative ℚ G -
      C 890 * (X * derivative ℚ G) -
      C 814 * (X ^ 2 * derivative ℚ G) -
      C 720 * G -
      C 896 * (X * G) = 0 := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := nz_ofNat 2
  have h64 : (64 : ℚ⟦X⟧) ≠ 0 := nz_ofNat 64
  have hSqDerivative : 2 * S * derivative ℚ S = -4 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hRadicalODE : (1 - 4 * X) * derivative ℚ S = -2 * S := by
    apply mul_left_cancel₀ hTwo
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  have hS3 : S ^ 3 = (1 - 4 * X) * S := by
    rw [show S ^ 3 = S ^ 2 * S by ring, hSq]
  have hS4 : S ^ 4 = (1 - 4 * X) ^ 2 := by
    rw [show S ^ 4 = (S ^ 2) ^ 2 by ring, hSq]
  have hS5 : S ^ 5 = (1 - 4 * X) ^ 2 * S := by
    rw [show S ^ 5 = (S ^ 2) ^ 2 * S by ring, hSq]
  have hS6 : S ^ 6 = (1 - 4 * X) ^ 3 := by
    rw [show S ^ 6 = (S ^ 2) ^ 3 by ring, hSq]
  have hpoly : 2 * (1 - S) ^ 5 * (3 * S + 1 - 4 * X) =
      64 * ((-1 + 6 * X - 7 * X ^ 2 - 4 * X ^ 3) + (1 - 4 * X + X ^ 2 + 2 * X ^ 3) * S) := by
    ring_nf
    rw [hS6, hS5, hS4, hS3, hSq]
    ring
  have h0 : 2 * (1 - 4 * X) * (2 + X) * X ^ 5 * G =
      (-1 + 6 * X - 7 * X ^ 2 - 4 * X ^ 3) + (1 - 4 * X + X ^ 2 + 2 * X ^ 3) * S := by
    apply mul_left_cancel₀ h64
    have hm := congrArg (fun f : ℚ⟦X⟧ => (2 * X) ^ 5 * (3 * S + 1 - 4 * X) * f) hG
    have hr : (2 * X) ^ 5 * (3 * S + 1 - 4 * X) * (2 * c ^ 5) =
        2 * (1 - S) ^ 5 * (3 * S + 1 - 4 * X) := by
      rw [show (2 * X) ^ 5 * (3 * S + 1 - 4 * X) * (2 * c ^ 5) =
        2 * (2 * X * c) ^ 5 * (3 * S + 1 - 4 * X) by ring, hc]
    rw [hr, hpoly] at hm
    linear_combination hm - 9 * (2 * X) ^ 5 * G * hSq
  have hd0 := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) h0
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd0
  have h1 : (20 * X ^ 4 - 164 * X ^ 5 + 280 * X ^ 6 + 224 * X ^ 7) * G +
      (4 * X ^ 5 - 30 * X ^ 6 + 48 * X ^ 7 + 32 * X ^ 8) * derivative ℚ G =
      (6 - 38 * X + 44 * X ^ 2 + 48 * X ^ 3) + (-6 + 26 * X - 4 * X ^ 2 - 28 * X ^ 3) * S := by
    linear_combination (1 - 4 * X) * hd0 + (1 - 4 * X + X ^ 2 + 2 * X ^ 3) * hRadicalODE
  have hd1 := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) h1
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd1
  have h2 : (80 * X ^ 3 - 1140 * X ^ 4 + 4960 * X ^ 5 - 5152 * X ^ 6 - 6272 * X ^ 7) * G +
      (40 * X ^ 4 - 504 * X ^ 5 + 1992 * X ^ 6 - 1984 * X ^ 7 - 1920 * X ^ 8) * derivative ℚ G +
      (4 * X ^ 5 - 46 * X ^ 6 + 168 * X ^ 7 - 160 * X ^ 8 - 128 * X ^ 9) *
        derivative ℚ (derivative ℚ G) =
      (-38 + 240 * X - 208 * X ^ 2 - 576 * X ^ 3) +
        (38 - 164 * X - 44 * X ^ 2 + 392 * X ^ 3) * S := by
    linear_combination (1 - 4 * X) * hd1 + (-6 + 26 * X - 4 * X ^ 2 - 28 * X ^ 3) * hRadicalODE
  have hd2 := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) h2
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd2
  have h3 : (240 * X ^ 2 - 5520 * X ^ 3 + 43040 * X ^ 4 - 130112 * X ^ 5 +
        79744 * X ^ 6 + 175616 * X ^ 7) * G +
      (240 * X ^ 3 - 4620 * X ^ 4 + 31552 * X ^ 5 - 86688 * X ^ 6 +
        54528 * X ^ 7 + 86528 * X ^ 8) * derivative ℚ G +
      (60 * X ^ 4 - 1020 * X ^ 5 + 6288 * X ^ 6 - 15936 * X ^ 7 +
        9984 * X ^ 8 + 12288 * X ^ 9) * derivative ℚ (derivative ℚ G) +
      (4 * X ^ 5 - 62 * X ^ 6 + 352 * X ^ 7 - 832 * X ^ 8 + 512 * X ^ 9 + 512 * X ^ 10) *
        derivative ℚ (derivative ℚ (derivative ℚ G)) =
      (240 - 1376 * X - 64 * X ^ 2 + 6912 * X ^ 3) +
        (-240 + 896 * X + 1616 * X ^ 2 - 5488 * X ^ 3) * S := by
    linear_combination (1 - 4 * X) * hd2 + (38 - 164 * X - 44 * X ^ 2 + 392 * X ^ 3) * hRadicalODE
  rw [map_ofNat C 6, map_ofNat C 21, map_ofNat C 12, map_ofNat C 62,
    map_ofNat C 268, map_ofNat C 190, map_ofNat C 120, map_ofNat C 890,
    map_ofNat C 814, map_ofNat C 720, map_ofNat C 896]
  have hM : (2 * (1 - 4 * X) ^ 4 * (2 + X) * X ^ 5 : ℚ⟦X⟧) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hTwo (pow_ne_zero 4 nz_one_sub_4X)) nz_two_add_X)
      (pow_ne_zero 5 nz_X)
  apply mul_left_cancel₀ hM
  linear_combination (240 - 3384 * X + 15144 * X ^ 2 - 18432 * X ^ 3 - 13440 * X ^ 4) * h0 +
    (40 - 728 * X + 4026 * X ^ 2 - 5992 * X ^ 3 - 4096 * X ^ 4) * h1 +
    (-28 * X + 294 * X ^ 2 - 630 * X ^ 3 - 392 * X ^ 4) * h2 +
    (6 * X ^ 2 - 21 * X ^ 3 - 12 * X ^ 4) * h3

private theorem coeff_X_pow_mul_zero (r m : ℕ) (p : ℚ⟦X⟧) (h : m < r) :
    coeff m (X ^ r * p) = 0 := by
  induction r generalizing m p with
  | zero => omega
  | succ r ih =>
    rw [pow_succ', mul_assoc]
    cases m with
    | zero => simp
    | succ m =>
      rw [coeff_succ_X_mul]
      exact ih m p (by omega)

private theorem coeff_succ_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 1) (derivative ℚ G) = ((k : ℚ) + 2) * coeff (k + 2) G := by
  rw [coeff_derivative]
  push_cast
  ring

private theorem coeff_succ_X_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 1) (X * derivative ℚ G) = ((k : ℚ) + 1) * coeff (k + 1) G := by
  rw [coeff_succ_X_mul, coeff_derivative]
  ring

private theorem coeff_succ_X2_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 1) (X ^ 2 * derivative ℚ G) = (k : ℚ) * coeff k G := by
  cases k with
  | zero => simp [coeff_X_pow_mul_zero 2 1 _ (by omega)]
  | succ k =>
    rw [show k + 1 + 1 = k + 2 by omega, coeff_X_pow_mul, coeff_derivative]
    push_cast
    ring

private theorem coeff_succ_X_derivative2 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 1) (X * derivative ℚ (derivative ℚ G)) =
      ((k : ℚ) + 1) * ((k : ℚ) + 2) * coeff (k + 2) G := by
  rw [coeff_succ_X_mul, coeff_derivative, coeff_derivative]
  push_cast
  ring

private theorem coeff_succ_X2_derivative2 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 1) (X ^ 2 * derivative ℚ (derivative ℚ G)) =
      (k : ℚ) * ((k : ℚ) + 1) * coeff (k + 1) G := by
  cases k with
  | zero => simp [coeff_X_pow_mul_zero 2 1 _ (by omega)]
  | succ k =>
    rw [show k + 1 + 1 = k + 2 by omega, coeff_X_pow_mul, coeff_derivative, coeff_derivative]
    push_cast
    ring

private theorem coeff_succ_X3_derivative2 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 1) (X ^ 3 * derivative ℚ (derivative ℚ G)) =
      ((k : ℚ) - 1) * (k : ℚ) * coeff k G := by
  rcases k with _ | _ | k
  · simp [coeff_X_pow_mul_zero 3 1 _ (by omega)]
  · simp [coeff_X_pow_mul_zero 3 2 _ (by omega)]
  · rw [show k + 1 + 1 + 1 = k + 3 by omega, coeff_X_pow_mul, coeff_derivative, coeff_derivative]
    push_cast
    ring

private theorem coeff_succ_X2_derivative3 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 1) (X ^ 2 * derivative ℚ (derivative ℚ (derivative ℚ G))) =
      (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) * coeff (k + 2) G := by
  cases k with
  | zero => simp [coeff_X_pow_mul_zero 2 1 _ (by omega)]
  | succ k =>
    rw [show k + 1 + 1 = k + 2 by omega, coeff_X_pow_mul,
      coeff_derivative, coeff_derivative, coeff_derivative]
    push_cast
    ring

private theorem coeff_succ_X3_derivative3 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 1) (X ^ 3 * derivative ℚ (derivative ℚ (derivative ℚ G))) =
      ((k : ℚ) - 1) * (k : ℚ) * ((k : ℚ) + 1) * coeff (k + 1) G := by
  rcases k with _ | _ | k
  · simp [coeff_X_pow_mul_zero 3 1 _ (by omega)]
  · simp [coeff_X_pow_mul_zero 3 2 _ (by omega)]
  · rw [show k + 1 + 1 + 1 = k + 3 by omega, coeff_X_pow_mul,
      coeff_derivative, coeff_derivative, coeff_derivative]
    push_cast
    ring

private theorem coeff_succ_X4_derivative3 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 1) (X ^ 4 * derivative ℚ (derivative ℚ (derivative ℚ G))) =
      ((k : ℚ) - 2) * ((k : ℚ) - 1) * (k : ℚ) * coeff k G := by
  rcases k with _ | _ | _ | k
  · simp [coeff_X_pow_mul_zero 4 1 _ (by omega)]
  · simp [coeff_X_pow_mul_zero 4 2 _ (by omega)]
  · simp [coeff_X_pow_mul_zero 4 3 _ (by omega)]
  · rw [show k + 1 + 1 + 1 + 1 = k + 4 by omega, coeff_X_pow_mul,
      coeff_derivative, coeff_derivative, coeff_derivative]
    push_cast
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a172062.main := by
  intro S c G hSq _ hc hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hode := congrArg (coeff (k + 1)) (generating_function_ode S c G hSq hc hG)
  simp only [map_add, map_sub, map_zero, coeff_C_mul] at hode
  rw [coeff_succ_X2_derivative3, coeff_succ_X3_derivative3, coeff_succ_X4_derivative3,
    coeff_succ_X_derivative2, coeff_succ_X2_derivative2, coeff_succ_X3_derivative2,
    coeff_succ_derivative, coeff_succ_X_derivative, coeff_succ_X2_derivative,
    coeff_succ_X_mul] at hode
  simp only [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  push_cast at hode ⊢
  linear_combination hode
