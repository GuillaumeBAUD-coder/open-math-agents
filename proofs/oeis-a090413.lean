import OMAStatements.S_oeis_a090413

/-!
Proof of OEIS A090413: the generating function satisfies
(3*X - 8*X^2)*S^2 + (1 - 6*X)*S - 1 = 0, whose radical Q satisfies Q^2 = 1 + 4*X^2.
Differentiating gives an exact linear differential equation whose n-th coefficient
is the claimed recurrence for n >= 3.
-/

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a090413.main := by
  have hsub : HasSubst (-(X : PowerSeries ℚ) ^ 2) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  have hcatQ : (catalanSeries.map (Nat.castRingHom ℚ)) ^ 2 * X + 1 =
      catalanSeries.map (Nat.castRingHom ℚ) := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
    simpa [PowerSeries.map_X] using h
  have hcat : OMA.S_oeis_a090413.catNeg ^ 2 * (-(X : PowerSeries ℚ) ^ 2) + 1 =
      OMA.S_oeis_a090413.catNeg := by
    have h := congrArg (substAlgHom hsub) hcatQ
    rw [map_add, map_mul, map_pow, map_one, substAlgHom_X] at h
    simpa [coe_substAlgHom, OMA.S_oeis_a090413.catNeg] using h
  have hcc : constantCoeff (1 - 3 * (X : PowerSeries ℚ) * OMA.S_oeis_a090413.catNeg) ≠ 0 := by
    simp
  have hrel : OMA.S_oeis_a090413.series *
      (1 - 3 * (X : PowerSeries ℚ) * OMA.S_oeis_a090413.catNeg) =
      OMA.S_oeis_a090413.catNeg :=
    (PowerSeries.eq_mul_inv_iff_mul_eq hcc).mp rfl
  let S := OMA.S_oeis_a090413.series
  have hU : (1 + 3 * X * S) * OMA.S_oeis_a090413.catNeg = S := by
    linear_combination -hrel
  have hU2 : (1 + 3 * X * S) ^ 2 * OMA.S_oeis_a090413.catNeg ^ 2 = S ^ 2 := by
    rw [← mul_pow, hU]
  have hquad : (3 * X - 8 * X ^ 2) * S ^ 2 + (1 - 6 * X) * S - 1 = 0 := by
    have hmul := congrArg ((1 + 3 * X * S) ^ 2 * ·) hcat
    have h1 : (1 + 3 * X * S) ^ 2 * (OMA.S_oeis_a090413.catNeg ^ 2 * (-X ^ 2) + 1) =
        ((1 + 3 * X * S) ^ 2 * OMA.S_oeis_a090413.catNeg ^ 2) * (-X ^ 2) + (1 + 3 * X * S) ^ 2 := by
      ring
    have h2 : (1 + 3 * X * S) ^ 2 * OMA.S_oeis_a090413.catNeg =
        (1 + 3 * X * S) * ((1 + 3 * X * S) * OMA.S_oeis_a090413.catNeg) := by
      ring
    rw [h1, hU2, h2, hU] at hmul
    linear_combination -hmul
  let Q : PowerSeries ℚ := (6 * X - 16 * X ^ 2) * S + (1 - 6 * X)
  have hQ2 : Q ^ 2 = 1 + 4 * X ^ 2 := by
    dsimp [Q]
    linear_combination 4 * (3 * X - 8 * X ^ 2) * hquad
  have hdX : d⁄dX (X : PowerSeries ℚ) = 1 := derivative_X
  have hd3 : d⁄dX (3 : PowerSeries ℚ) = 0 := derivative_C
  have hd4 : d⁄dX (4 : PowerSeries ℚ) = 0 := derivative_C
  have hd6 : d⁄dX (6 : PowerSeries ℚ) = 0 := derivative_C
  have hd8 : d⁄dX (8 : PowerSeries ℚ) = 0 := derivative_C
  have hd16 : d⁄dX (16 : PowerSeries ℚ) = 0 := derivative_C
  have hd3X : d⁄dX (3 * (X : PowerSeries ℚ)) = 3 := by
    rw [Derivation.leibniz, hd3, hdX, smul_eq_mul, smul_zero, add_zero, mul_one]
  have hd6X : d⁄dX (6 * (X : PowerSeries ℚ)) = 6 := by
    rw [Derivation.leibniz, hd6, hdX, smul_eq_mul, smul_zero, add_zero, mul_one]
  have hd4X2 : d⁄dX (4 * (X : PowerSeries ℚ) ^ 2) = 8 * X := by
    rw [Derivation.leibniz, hd4, derivative_pow, hdX, smul_eq_mul, smul_zero, add_zero]
    have h42 : (4 : PowerSeries ℚ) * ((2 : ℕ) : PowerSeries ℚ) = 8 := by norm_num
    simp only [Nat.add_one_sub_one, pow_one, mul_one]
    linear_combination X * h42
  have hd8X2 : d⁄dX (8 * (X : PowerSeries ℚ) ^ 2) = 16 * X := by
    rw [Derivation.leibniz, hd8, derivative_pow, hdX, smul_eq_mul, smul_zero, add_zero]
    have h82 : (8 : PowerSeries ℚ) * ((2 : ℕ) : PowerSeries ℚ) = 16 := by norm_num
    simp only [Nat.add_one_sub_one, pow_one, mul_one]
    linear_combination X * h82
  have hd16X2 : d⁄dX (16 * (X : PowerSeries ℚ) ^ 2) = 32 * X := by
    rw [Derivation.leibniz, hd16, derivative_pow, hdX, smul_eq_mul, smul_zero, add_zero]
    have h162 : (16 : PowerSeries ℚ) * ((2 : ℕ) : PowerSeries ℚ) = 32 := by norm_num
    simp only [Nat.add_one_sub_one, pow_one, mul_one]
    linear_combination X * h162
  have hdQ2 : Q * d⁄dX Q = 4 * (X : PowerSeries ℚ) := by
    have h := congrArg (fun f : PowerSeries ℚ => d⁄dX f) hQ2
    have hrhs : d⁄dX (1 + 4 * (X : PowerSeries ℚ) ^ 2) = 8 * X := by
      rw [map_add, Derivation.map_one_eq_zero, zero_add, hd4X2]
    rw [derivative_pow, hrhs] at h
    have h' := congrArg (C (1 / 2 : ℚ) * ·) h
    have hc2 : C (1 / 2 : ℚ) * ((2 : ℕ) : PowerSeries ℚ) = 1 := by
      rw [← map_natCast C 2, ← map_mul]
      norm_num
    have hc8 : C (1 / 2 : ℚ) * (8 : PowerSeries ℚ) = 4 := by
      rw [show (8 : PowerSeries ℚ) = C (8 : ℚ) from rfl, ← map_mul]
      norm_num
      rfl
    have hpow1 : Q ^ (2 - 1) = Q := by simp
    rw [hpow1] at h'
    linear_combination h' - Q * d⁄dX Q * hc2 + X * hc8
  have hdQ : d⁄dX Q = (6 - 32 * X) * S + (6 * X - 16 * X ^ 2) * d⁄dX S - 6 := by
    dsimp [Q]
    rw [map_add, Derivation.leibniz, map_sub, hd6X, hd16X2, map_sub,
      Derivation.map_one_eq_zero, hd6X, smul_eq_mul, smul_eq_mul]
    ring
  let L : PowerSeries ℚ :=
    d⁄dX ((3 * X - 8 * X ^ 2) * S) + X ^ 3 * (12 * d⁄dX S - 32 * d⁄dX (X * S))
  have hL_eq : L = (3 - 16 * X - 32 * X ^ 3) * S +
      (3 * X - 8 * X ^ 2) * (1 + 4 * X ^ 2) * d⁄dX S := by
    dsimp [L]
    rw [Derivation.leibniz, map_sub, hd3X, hd8X2, Derivation.leibniz, hdX,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  have h2L : 2 * L = 2 * (3 + 2 * X) := by
    dsimp [Q] at hdQ2 hQ2
    linear_combination 2 * hL_eq - (1 + 4 * X ^ 2) * hdQ -
      d⁄dX Q * hQ2 + ((6 * X - 16 * X ^ 2) * S + (1 - 6 * X)) * hdQ2
  intro n hn
  have hcoeff : coeff n (2 * L) = coeff n (2 * (3 + 2 * (X : PowerSeries ℚ))) :=
    congrArg (coeff n) h2L
  simp only [coeff_ofNat_mul, map_add] at hcoeff
  have hc3 : coeff n (3 : PowerSeries ℚ) = 0 := by
    rw [show (3 : PowerSeries ℚ) = C (3 : ℚ) from rfl, coeff_C, ite_eq_right]
    omega
  have hcX : coeff n (X : PowerSeries ℚ) = 0 := by
    rw [coeff_X, ite_eq_right]
    omega
  rw [hc3, hcX] at hcoeff
  have hLn : coeff n L = 0 := by linarith
  dsimp [L] at hLn
  rw [map_add, coeff_derivative] at hLn
  have hc1 : coeff (n + 1) ((3 * X - 8 * X ^ 2) * S) =
      3 * OMA.S_oeis_a090413.term n - 8 * OMA.S_oeis_a090413.term (n - 1) := by
    rw [sub_mul, map_sub, mul_assoc, mul_assoc, coeff_ofNat_mul, coeff_ofNat_mul,
      coeff_succ_X_mul]
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [show X ^ 2 * S = X * (X * S) by ring, hk, coeff_succ_X_mul, coeff_succ_X_mul]
    rfl
  have hc2 : coeff n (X ^ 3 * (12 * d⁄dX S - 32 * d⁄dX (X * S))) =
      12 * ((n : ℚ) - 2) * OMA.S_oeis_a090413.term (n - 2) +
        32 * (2 - (n : ℚ)) * OMA.S_oeis_a090413.term (n - 3) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [coeff_X_pow_mul, map_sub, coeff_ofNat_mul, coeff_ofNat_mul,
      coeff_derivative, coeff_derivative, coeff_succ_X_mul]
    simp only [OMA.S_oeis_a090413.term, S, show m + 3 - 2 = m + 1 by omega,
      show m + 3 - 3 = m by omega]
    push_cast
    ring
  rw [hc1, hc2] at hLn
  linear_combination hLn
