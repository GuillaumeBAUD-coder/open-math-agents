import OMAStatements.S_oeis_a117187

-- Problem: A117187: Expansion of (1+x)c(x^2)/((1-x^2*c(x^2))sqrt(1-4x^2)), c(x) the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a117187.lean:0 (declaration OMA.S_oeis_a117187.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A117187Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (X ^ 2 - 4 * X ^ 4 + (X ^ 2) * S) = 1 + X + (-1 - X) * S) :
    (16 * X + 16 * X ^ 2 - 96 * X ^ 3 - 96 * X ^ 4 + 128 * X ^ 5 + 128 * X ^ 6) * derivative ℚ G + (64 + 48 * X - 384 * X ^ 2 - 288 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) * G = 64 + 128 * X + 64 * X ^ 2 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have hS2 : S * S = (1 - 4 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-4 * X ^ 6 + 16 * X ^ 8) * G = (2 * X ^ 2 + 2 * X ^ 3 - 8 * X ^ 4 - 8 * X ^ 5 : ℚ⟦X⟧) + (-2 * X ^ 2 - 2 * X ^ 3 + 4 * X ^ 4 + 4 * X ^ 5) * S := by
    linear_combination (X ^ 2 - 4 * X ^ 4 - (X ^ 2) * S) * hG + (X ^ 2) * ((X ^ 2) * G - (-1 - X)) * hS
  have hPd : derivative ℚ (1 - 4 * (X * X) : ℚ⟦X⟧) = -8 * X := by
    simp [Derivation.leibniz, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-4 * (X * X * X * X * X * X) + 16 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-24 * X ^ 5 + 128 * X ^ 7) * G + (-4 * X ^ 6 + 16 * X ^ 8) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d16]
    ring
  have hR : derivative ℚ ((2 * (X * X) + 2 * (X * X * X) - 8 * (X * X * X * X) - 8 * (X * X * X * X * X) : ℚ⟦X⟧) + (-2 * (X * X) - 2 * (X * X * X) + 4 * (X * X * X * X) + 4 * (X * X * X * X * X) : ℚ⟦X⟧) * S) =
      4 * X + 6 * X ^ 2 - 32 * X ^ 3 - 40 * X ^ 4 + (-4 * X - 6 * X ^ 2 + 16 * X ^ 3 + 20 * X ^ 4) * S + (-2 * X ^ 2 - 2 * X ^ 3 + 4 * X ^ 4 + 4 * X ^ 5) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d4, d8]
    ring
  have hk2 : (-4 * (X * X * X * X * X * X) + 16 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (2 * (X * X) + 2 * (X * X * X) - 8 * (X * X * X * X) - 8 * (X * X * X * X * X) : ℚ⟦X⟧) + (-2 * (X * X) - 2 * (X * X * X) + 4 * (X * X * X * X) + 4 * (X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-24 * X ^ 5 + 128 * X ^ 7) * G + (-4 * X ^ 6 + 16 * X ^ 8) * derivative ℚ G =
      4 * X + 6 * X ^ 2 - 32 * X ^ 3 - 40 * X ^ 4 + (-4 * X - 6 * X ^ 2 + 16 * X ^ 3 + 20 * X ^ 4) * S + (-2 * X ^ 2 - 2 * X ^ 3 + 4 * X ^ 4 + 4 * X ^ 5) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 7 * ((1 - 4 * X ^ 2) * ((16 * X + 16 * X ^ 2 - 96 * X ^ 3 - 96 * X ^ 4 + 128 * X ^ 5 + 128 * X ^ 6) * derivative ℚ G + (64 + 48 * X - 384 * X ^ 2 - 288 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) * G - (64 + 128 * X + 64 * X ^ 2))) = 0 := by
    linear_combination (-2 * X ^ 2 - 2 * X ^ 3 + 4 * X ^ 4 + 4 * X ^ 5) ^ 2 * S * hdS - 2 * (-2 * X ^ 2 - 2 * X ^ 3 + 4 * X ^ 4 + 4 * X ^ 5) ^ 2 * derivative ℚ S * hS -
      (2 * (-4 * X - 6 * X ^ 2 + 16 * X ^ 3 + 20 * X ^ 4) * (1 - 4 * X ^ 2) + (-2 * X ^ 2 - 2 * X ^ 3 + 4 * X ^ 4 + 4 * X ^ 5) * (-8 * X)) * hk + 2 * (-2 * X ^ 2 - 2 * X ^ 3 + 4 * X ^ 4 + 4 * X ^ 5) * (1 - 4 * X ^ 2) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 7 ≠ 0 := pow_ne_zero 7 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 4 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (X ^ 2 - 4 * X ^ 4 + (X ^ 2) * S) = 1 + X + (-1 - X) * S) :
    (31 * X ^ 2 + 37 * X ^ 3 - 124 * X ^ 4 - 148 * X ^ 5) * derivative ℚ (derivative ℚ G) + (143 * X + 135 * X ^ 2 - 944 * X ^ 3 - 984 * X ^ 4) * derivative ℚ G + (-48 - 95 * X - 1240 * X ^ 2 - 1080 * X ^ 3) * G =
      -48 := by
  have h := key S G hS hG
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d96 : derivative ℚ (96 : ℚ⟦X⟧) = 0 := dnum 96
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have d288 : derivative ℚ (288 : ℚ⟦X⟧) = 0 := dnum 288
  have d384 : derivative ℚ (384 : ℚ⟦X⟧) = 0 := dnum 384
  have hL : derivative ℚ ((16 * X + 16 * (X * X) - 96 * (X * X * X) - 96 * (X * X * X * X) + 128 * (X * X * X * X * X) + 128 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (64 + 48 * X - 384 * (X * X) - 288 * (X * X * X) + 384 * (X * X * X * X) + 256 * (X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (16 + 32 * X - 288 * X ^ 2 - 384 * X ^ 3 + 640 * X ^ 4 + 768 * X ^ 5) * derivative ℚ G + (16 * X + 16 * X ^ 2 - 96 * X ^ 3 - 96 * X ^ 4 + 128 * X ^ 5 + 128 * X ^ 6) * derivative ℚ (derivative ℚ G) + (48 - 768 * X - 864 * X ^ 2 + 1536 * X ^ 3 + 1280 * X ^ 4) * G + (64 + 48 * X - 384 * X ^ 2 - 288 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d16, d48, d64, d96, d128, d256, d288, d384]
    ring
  have hRd : derivative ℚ (64 + 128 * X + 64 * (X * X) : ℚ⟦X⟧) = 128 + 128 * X := by
    simp [Derivation.leibniz, d64, d128]
    ring
  have h2 : (16 * X + 16 * (X * X) - 96 * (X * X * X) - 96 * (X * X * X * X) + 128 * (X * X * X * X * X) + 128 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (64 + 48 * X - 384 * (X * X) - 288 * (X * X * X) + 384 * (X * X * X * X) + 256 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (64 + 128 * X + 64 * (X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (16 + 32 * X - 288 * X ^ 2 - 384 * X ^ 3 + 640 * X ^ 4 + 768 * X ^ 5) * derivative ℚ G + (16 * X + 16 * X ^ 2 - 96 * X ^ 3 - 96 * X ^ 4 + 128 * X ^ 5 + 128 * X ^ 6) * derivative ℚ (derivative ℚ G) + (48 - 768 * X - 864 * X ^ 2 + 1536 * X ^ 3 + 1280 * X ^ 4) * G + (64 + 48 * X - 384 * X ^ 2 - 288 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) * derivative ℚ G = 128 + 128 * X := by
    rw [← hL, h2, hRd]
  have hfull : (16 + 16 * X - 32 * X ^ 2 - 32 * X ^ 3) * ((31 * X ^ 2 + 37 * X ^ 3 - 124 * X ^ 4 - 148 * X ^ 5) * derivative ℚ (derivative ℚ G) + (143 * X + 135 * X ^ 2 - 944 * X ^ 3 - 984 * X ^ 4) * derivative ℚ G + (-48 - 95 * X - 1240 * X ^ 2 - 1080 * X ^ 3) * G - (-48)) = 0 := by
    linear_combination (31 * X + 37 * X ^ 2) * hd + (-12 - 50 * X) * h
  have hg : (16 + 16 * X - 32 * X ^ 2 - 32 * X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (16 : ℚ⟦X⟧) = 16 := cnum 16
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (X ^ 2 - 4 * X ^ 4 + (X ^ 2) * S) = 1 + X + (-1 - X) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C 31 + derivative ℚ (derivative ℚ G) * X * X * X * C 37 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-124) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-148) +
      derivative ℚ G * X * C 143 + derivative ℚ G * X * X * C 135 +
      derivative ℚ G * X * X * X * C (-944) + derivative ℚ G * X * X * X * X * C (-984) +
      G * C (-48) + G * X * C (-95) +
      G * X * X * C (-1240) + G * X * X * X * C (-1080) =
      C (-48) := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (X ^ 2 - 4 * X ^ 4 + (X ^ 2) * S) = 1 + X + (-1 - X) * S) (m : ℕ) :
    31 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 37 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      (-124) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-148) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      143 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 135 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-944) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-984) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-48) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-95) * coeff (m + 1 + 1 + 1 + 1) G +
      (-1240) * coeff (m + 1 + 1 + 1) G + (-1080) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (X ^ 2 - 4 * X ^ 4 + (X ^ 2) * S) = 1 + X + (-1 - X) * S) :
    186 * coeff (0 + 1 + 1 + 1) G + 74 * coeff (0 + 1 + 1) G +
      429 * coeff (0 + 1 + 1 + 1) G + 270 * coeff (0 + 1 + 1) G +
      (-944) * coeff (0 + 1) G + (-48) * coeff (0 + 1 + 1 + 1) G +
      (-95) * coeff (0 + 1 + 1) G + (-1240) * coeff (0 + 1) G +
      (-1080) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (X ^ 2 - 4 * X ^ 4 + (X ^ 2) * S) = 1 + X + (-1 - X) * S) :
    372 * coeff (0 + 1 + 1 + 1 + 1) G + 222 * coeff (0 + 1 + 1 + 1) G +
      (-248) * coeff (0 + 1 + 1) G + 572 * coeff (0 + 1 + 1 + 1 + 1) G +
      405 * coeff (0 + 1 + 1 + 1) G + (-1888) * coeff (0 + 1 + 1) G +
      (-984) * coeff (0 + 1) G + (-48) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-95) * coeff (0 + 1 + 1 + 1) G + (-1240) * coeff (0 + 1 + 1) G +
      (-1080) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A117187Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a117187.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  cases m with
  | zero =>
    have r := A117187Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (2 * PowerSeries.X ^ 2) * hG - ((-1 - PowerSeries.X) + (-PowerSeries.X ^ 2) * S * G) * hc - ((PowerSeries.X ^ 2) * G) * hS)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A117187Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination (2 * PowerSeries.X ^ 2) * hG - ((-1 - PowerSeries.X) + (-PowerSeries.X ^ 2) * S * G) * hc - ((PowerSeries.X ^ 2) * G) * hS)
      push_cast
      linear_combination r
    | succ m =>
      have r := A117187Aux.rel (S) G (by linear_combination hS)
          (by linear_combination (2 * PowerSeries.X ^ 2) * hG - ((-1 - PowerSeries.X) + (-PowerSeries.X ^ 2) * S * G) * hc - ((PowerSeries.X ^ 2) * G) * hS) m
      push_cast
      linear_combination r
