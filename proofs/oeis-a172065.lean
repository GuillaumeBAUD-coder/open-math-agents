import OMAStatements.S_oeis_a172065

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
    (hG : G * (3 * S - 1 + 4 * X) = 2 * c ^ 8) :
    C 6 * (X ^ 2 * derivative ℚ (derivative ℚ (derivative ℚ G))) -
      C 21 * (X ^ 3 * derivative ℚ (derivative ℚ (derivative ℚ G))) -
      C 12 * (X ^ 4 * derivative ℚ (derivative ℚ (derivative ℚ G))) +
      C 92 * (X * derivative ℚ (derivative ℚ G)) -
      C 373 * (X ^ 2 * derivative ℚ (derivative ℚ G)) -
      C 250 * (X ^ 3 * derivative ℚ (derivative ℚ G)) +
      C 288 * derivative ℚ G -
      C 1868 * (X * derivative ℚ G) -
      C 1480 * (X ^ 2 * derivative ℚ G) -
      C 2592 * G -
      C 2420 * (X * G) = 0 := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := nz_ofNat 2
  have h512 : (512 : ℚ⟦X⟧) ≠ 0 := nz_ofNat 512
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
  have hS7 : S ^ 7 = (1 - 4 * X) ^ 3 * S := by
    rw [show S ^ 7 = (S ^ 2) ^ 3 * S by ring, hSq]
  have hS8 : S ^ 8 = (1 - 4 * X) ^ 4 := by
    rw [show S ^ 8 = (S ^ 2) ^ 4 by ring, hSq]
  have hS9 : S ^ 9 = (1 - 4 * X) ^ 4 * S := by
    rw [show S ^ 9 = (S ^ 2) ^ 4 * S by ring, hSq]
  have hpoly : 2 * (1 - S) ^ 8 * (3 * S + 1 - 4 * X) =
      512 * ((-1 + 9 * X - 25 * X ^ 2 + 18 * X ^ 3 + 9 * X ^ 4 - 4 * X ^ 5) +
        (1 - 7 * X + 13 * X ^ 2 - 2 * X ^ 3 - 5 * X ^ 4) * S) := by
    ring_nf
    rw [hS9, hS8, hS7, hS6, hS5, hS4, hS3, hSq]
    ring
  have h0 : 2 * (1 - 4 * X) * (2 + X) * X ^ 8 * G =
      (-1 + 9 * X - 25 * X ^ 2 + 18 * X ^ 3 + 9 * X ^ 4 - 4 * X ^ 5) +
        (1 - 7 * X + 13 * X ^ 2 - 2 * X ^ 3 - 5 * X ^ 4) * S := by
    apply mul_left_cancel₀ h512
    have hm := congrArg (fun f : ℚ⟦X⟧ => (2 * X) ^ 8 * (3 * S + 1 - 4 * X) * f) hG
    have hr : (2 * X) ^ 8 * (3 * S + 1 - 4 * X) * (2 * c ^ 8) =
        2 * (1 - S) ^ 8 * (3 * S + 1 - 4 * X) := by
      rw [show (2 * X) ^ 8 * (3 * S + 1 - 4 * X) * (2 * c ^ 8) =
        2 * (2 * X * c) ^ 8 * (3 * S + 1 - 4 * X) by ring, hc]
    rw [hr, hpoly] at hm
    linear_combination hm - 9 * (2 * X) ^ 8 * G * hSq
  have hd0 := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) h0
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd0
  have h1 : (32 * X ^ 7 - 254 * X ^ 8 + 424 * X ^ 9 + 320 * X ^ 10) * G +
      (4 * X ^ 8 - 30 * X ^ 9 + 48 * X ^ 10 + 32 * X ^ 11) * derivative ℚ G =
      (9 - 86 * X + 254 * X ^ 2 - 180 * X ^ 3 - 164 * X ^ 4 + 80 * X ^ 5) +
        (-9 + 68 * X - 136 * X ^ 2 + 8 * X ^ 3 + 90 * X ^ 4) * S := by
    linear_combination (1 - 4 * X) * hd0 +
      (1 - 7 * X + 13 * X ^ 2 - 2 * X ^ 3 - 5 * X ^ 4) * hRadicalODE
  have hd1 := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) h1
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd1
  have h2 : (224 * X ^ 6 - 2928 * X ^ 7 + 11944 * X ^ 8 - 12064 * X ^ 9 - 12800 * X ^ 10) * G +
      (64 * X ^ 7 - 780 * X ^ 8 + 3000 * X ^ 9 - 2944 * X ^ 10 - 2688 * X ^ 11) * derivative ℚ G +
      (4 * X ^ 8 - 46 * X ^ 9 + 168 * X ^ 10 - 160 * X ^ 11 - 128 * X ^ 12) *
        derivative ℚ (derivative ℚ G) =
      (-86 + 852 * X - 2572 * X ^ 2 + 1504 * X ^ 3 + 3024 * X ^ 4 - 1600 * X ^ 5) +
        (86 - 680 * X + 1384 * X ^ 2 + 248 * X ^ 3 - 1620 * X ^ 4) * S := by
    linear_combination (1 - 4 * X) * hd1 +
      (-9 + 68 * X - 136 * X ^ 2 + 8 * X ^ 3 + 90 * X ^ 4) * hRadicalODE
  have hd2 := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) h2
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd2
  have h3 : (1344 * X ^ 5 - 25872 * X ^ 6 + 177536 * X ^ 7 - 490784 * X ^ 8 +
        306304 * X ^ 9 + 512000 * X ^ 10) * G +
      (672 * X ^ 6 - 11856 * X ^ 7 + 75616 * X ^ 8 - 197280 * X ^ 9 +
        123648 * X ^ 10 + 169472 * X ^ 11) * derivative ℚ G +
      (96 * X ^ 7 - 1578 * X ^ 8 + 9456 * X ^ 9 - 23424 * X ^ 10 +
        14592 * X ^ 11 + 16896 * X ^ 12) * derivative ℚ (derivative ℚ G) +
      (4 * X ^ 8 - 62 * X ^ 9 + 352 * X ^ 10 - 832 * X ^ 11 + 512 * X ^ 12 + 512 * X ^ 13) *
        derivative ℚ (derivative ℚ (derivative ℚ G)) =
      (852 - 8552 * X + 25088 * X ^ 2 - 5952 * X ^ 3 - 56384 * X ^ 4 + 32000 * X ^ 5) +
        (-852 + 6848 * X - 13096 * X ^ 2 - 9952 * X ^ 3 + 29160 * X ^ 4) * S := by
    linear_combination (1 - 4 * X) * hd2 +
      (86 - 680 * X + 1384 * X ^ 2 + 248 * X ^ 3 - 1620 * X ^ 4) * hRadicalODE
  rw [map_ofNat C 6, map_ofNat C 21, map_ofNat C 12, map_ofNat C 92,
    map_ofNat C 373, map_ofNat C 250, map_ofNat C 288, map_ofNat C 1868,
    map_ofNat C 1480, map_ofNat C 2592, map_ofNat C 2420]
  have hM : (2 * (1 - 4 * X) ^ 4 * (2 + X) * X ^ 8 : ℚ⟦X⟧) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hTwo (pow_ne_zero 4 nz_one_sub_4X)) nz_two_add_X)
      (pow_ne_zero 8 nz_X)
  apply mul_left_cancel₀ hM
  linear_combination (1008 - 13224 * X + 54960 * X ^ 2 - 61248 * X ^ 3 - 46080 * X ^ 4) * h0 +
    (112 - 1904 * X + 9660 * X ^ 2 - 13048 * X ^ 3 - 9184 * X ^ 4) * h1 +
    (-52 * X + 474 * X ^ 2 - 918 * X ^ 3 - 584 * X ^ 4) * h2 +
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

theorem OMA.solution : type_of% @OMA.S_oeis_a172065.main := by
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
