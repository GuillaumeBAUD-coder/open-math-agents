import OMAStatements.S_oeis_a185966

-- Problem: A185966: Series reversion of A028310.
-- Upstream: formal-conjectures statements/oeis-a185966.lean:0 (declaration OMA.S_oeis_a185966.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A185966Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 + 2 * X : ℚ⟦X⟧) * G + (-X - X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (6 * X ^ 2 - X ^ 3 + 28 * X ^ 4 - 68 * X ^ 5 + 12 * X ^ 6) * derivative ℚ (derivative ℚ G) + (12 * X + 11 * X ^ 2 + 102 * X ^ 3 - 148 * X ^ 4 + 30 * X ^ 5) * derivative ℚ G + (13 * X + 36 * X ^ 2 - 12 * X ^ 3) * G =
      X + 12 * X ^ 2 - 6 * X ^ 3 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have hp0 : (-1 : ℚ⟦X⟧) + (1 + 2 * X : ℚ⟦X⟧) * G + (-1 * X - 1 * (X * X) : ℚ⟦X⟧) * G * G + (1 * (X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 : ℚ⟦X⟧) + (1 + 2 * X : ℚ⟦X⟧) * G + (-1 * X - 1 * (X * X) : ℚ⟦X⟧) * G * G + (1 * (X * X) : ℚ⟦X⟧) * G * G * G) =
      (1 + 2 * X : ℚ⟦X⟧) * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G + (-2 * X - 2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1 - 2 * X : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2]
    ring
  have hd1 : (1 + 2 * X : ℚ⟦X⟧) * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G + (-2 * X - 2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1 - 2 * X : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (1 + 2 * X : ℚ⟦X⟧) * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G + (-2 * X - 2 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1 - 2 * X : ℚ⟦X⟧) * G * G + (3 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((1 + 2 * X : ℚ⟦X⟧) * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G + (-2 * X - 2 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1 - 2 * X : ℚ⟦X⟧) * G * G + (3 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G * G * G) =
      (1 + 2 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 * X - 2 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 * X - 2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-4 - 8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hd2 : (1 + 2 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 * X - 2 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 * X - 2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-4 - 8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((1 + 2 * X : ℚ⟦X⟧) + (-2 * X - 2 * X ^ 2 : ℚ⟦X⟧) * G + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2) ^ 3 * ((6 * X ^ 2 - X ^ 3 + 28 * X ^ 4 - 68 * X ^ 5 + 12 * X ^ 6) * derivative ℚ (derivative ℚ G) + (12 * X + 11 * X ^ 2 + 102 * X ^ 3 - 148 * X ^ 4 + 30 * X ^ 5) * derivative ℚ G + (13 * X + 36 * X ^ 2 - 12 * X ^ 3) * G - (X + 12 * X ^ 2 - 6 * X ^ 3)) = 0 := by
    linear_combination ((X + 18 * X ^ 2 + 78 * X ^ 3 + 116 * X ^ 4 + 24 * X ^ 5 - 48 * X ^ 6 : ℚ⟦X⟧) + (12 * X - 30 * X ^ 2 - 48 * X ^ 3 - 164 * X ^ 4 - 520 * X ^ 5 + 144 * X ^ 6 + 96 * X ^ 7 : ℚ⟦X⟧) * G + (-48 * X ^ 2 + 90 * X ^ 3 + 168 * X ^ 4 + 338 * X ^ 5 + 584 * X ^ 6 - 384 * X ^ 7 - 48 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 + (48 * X ^ 3 - 116 * X ^ 4 - 132 * X ^ 5 - 368 * X ^ 6 - 160 * X ^ 7 + 240 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 + (-36 * X ^ 4 + 123 * X ^ 5 - 24 * X ^ 6 + 300 * X ^ 7 - 180 * X ^ 8 : ℚ⟦X⟧) * G ^ 4) * hP +
      ((12 * X + 35 * X ^ 2 + 150 * X ^ 3 + 200 * X ^ 4 - 106 * X ^ 5 + 24 * X ^ 6 + 24 * X ^ 7 : ℚ⟦X⟧) + (12 * X ^ 3 + 34 * X ^ 4 + 74 * X ^ 5 + 28 * X ^ 6 - 272 * X ^ 7 - 200 * X ^ 8 + 48 * X ^ 9 : ℚ⟦X⟧) * (derivative ℚ G) + (-24 * X ^ 2 - 72 * X ^ 3 - 424 * X ^ 4 - 452 * X ^ 5 + 88 * X ^ 6 - 296 * X ^ 7 : ℚ⟦X⟧) * G + (-60 * X ^ 4 - 110 * X ^ 5 - 284 * X ^ 6 + 124 * X ^ 7 + 1128 * X ^ 8 + 32 * X ^ 9 - 48 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ G) + (12 * X ^ 3 + 116 * X ^ 4 + 754 * X ^ 5 + 664 * X ^ 6 + 52 * X ^ 7 + 320 * X ^ 8 - 24 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 + (108 * X ^ 5 + 90 * X ^ 6 + 486 * X ^ 7 - 720 * X ^ 8 - 1008 * X ^ 9 + 216 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 * X ^ 4 - 110 * X ^ 5 - 660 * X ^ 6 - 320 * X ^ 7 - 448 * X ^ 8 + 24 * X ^ 9 : ℚ⟦X⟧) * G ^ 3 + (-108 * X ^ 6 + 18 * X ^ 7 - 504 * X ^ 8 + 1224 * X ^ 9 - 216 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-36 * X ^ 5 + 123 * X ^ 6 + 246 * X ^ 7 + 300 * X ^ 8 - 18 * X ^ 9 : ℚ⟦X⟧) * G ^ 4) * hd1 +
      ((6 * X ^ 2 + 23 * X ^ 3 + 48 * X ^ 4 + 40 * X ^ 5 - 148 * X ^ 6 - 224 * X ^ 7 + 48 * X ^ 8 : ℚ⟦X⟧) + (-24 * X ^ 3 - 68 * X ^ 4 - 148 * X ^ 5 - 56 * X ^ 6 + 544 * X ^ 7 + 400 * X ^ 8 - 96 * X ^ 9 : ℚ⟦X⟧) * G + (60 * X ^ 4 + 110 * X ^ 5 + 284 * X ^ 6 - 124 * X ^ 7 - 1128 * X ^ 8 - 32 * X ^ 9 + 48 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 + (-72 * X ^ 5 - 60 * X ^ 6 - 324 * X ^ 7 + 480 * X ^ 8 + 672 * X ^ 9 - 144 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 + (54 * X ^ 6 - 9 * X ^ 7 + 252 * X ^ 8 - 612 * X ^ 9 + 108 * X ^ 10 : ℚ⟦X⟧) * G ^ 4) * hd2
  have hPG : (1 + 2 * X : ℚ⟦X⟧) + (-2 * X - 2 * X ^ 2 : ℚ⟦X⟧) * G + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 + 2 * X : ℚ⟦X⟧) * G + (-X - X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C 6 + derivative ℚ (derivative ℚ G) * X * X * X * C (-1) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 28 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-68) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 12 + derivative ℚ G * X * C 12 +
      derivative ℚ G * X * X * C 11 + derivative ℚ G * X * X * X * C 102 +
      derivative ℚ G * X * X * X * X * C (-148) + derivative ℚ G * X * X * X * X * X * C 30 +
      G * X * C 13 + G * X * X * C 36 +
      G * X * X * X * C (-12) =
      C 1 * X + C 12 * X * X +
      C (-6) * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 + 2 * X : ℚ⟦X⟧) * G + (-X - X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    6 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-1) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      28 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-68) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      12 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + 12 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      11 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 102 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-148) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 30 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      13 * coeff (m + 1 + 1 + 1 + 1 + 1) G + 36 * coeff (m + 1 + 1 + 1 + 1) G +
      (-12) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 + 2 * X : ℚ⟦X⟧) * G + (-X - X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    72 * coeff (0 + 1 + 1 + 1 + 1) G + (-6) * coeff (0 + 1 + 1 + 1) G +
      56 * coeff (0 + 1 + 1) G + 48 * coeff (0 + 1 + 1 + 1 + 1) G +
      33 * coeff (0 + 1 + 1 + 1) G + 204 * coeff (0 + 1 + 1) G +
      (-148) * coeff (0 + 1) G + 13 * coeff (0 + 1 + 1 + 1) G +
      36 * coeff (0 + 1 + 1) G + (-12) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 + 2 * X : ℚ⟦X⟧) * G + (-X - X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    120 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-12) * coeff (0 + 1 + 1 + 1 + 1) G +
      168 * coeff (0 + 1 + 1 + 1) G + (-136) * coeff (0 + 1 + 1) G +
      60 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 44 * coeff (0 + 1 + 1 + 1 + 1) G +
      306 * coeff (0 + 1 + 1 + 1) G + (-296) * coeff (0 + 1 + 1) G +
      30 * coeff (0 + 1) G + 13 * coeff (0 + 1 + 1 + 1 + 1) G +
      36 * coeff (0 + 1 + 1 + 1) G + (-12) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A185966Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a185966.main := by
  intro T G _ hT hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  have hn : ((1) * PowerSeries.X) * ((1) * PowerSeries.X) = (PowerSeries.X ^ 2 : PowerSeries ℚ) := by
    linear_combination (0 : PowerSeries ℚ) * hT
  have hnu0 : (1 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp at h'
  have hnu : (PowerSeries.X ^ 2 : PowerSeries ℚ) ≠ 0 := by
    have e : (PowerSeries.X ^ 2 : PowerSeries ℚ) = PowerSeries.X ^ 2 * (1 : PowerSeries ℚ) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 2 PowerSeries.X_ne_zero) hnu0
  have hN1 : ((1) * PowerSeries.X : PowerSeries ℚ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn
    exact hnu hn.symm
  have hM : ((1) * PowerSeries.X) ^ 3 * ((-1 : PowerSeries ℚ) + (1 + 2 * PowerSeries.X : PowerSeries ℚ) * G + (-PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 3) = 0 := by
    linear_combination ((1) * PowerSeries.X ^ 2) * hT +
      ((1) * PowerSeries.X ^ 2 + (-1) * PowerSeries.X ^ 2 * T + (1) * PowerSeries.X ^ 2 * T ^ 2 + (2) * PowerSeries.X ^ 3 + (-1) * PowerSeries.X ^ 3 * T + (-1) * PowerSeries.X ^ 3 * G + (1) * PowerSeries.X ^ 3 * G * T + (-1) * PowerSeries.X ^ 4 * G + (1) * PowerSeries.X ^ 4 * G ^ 2) * hG
  have hP : (-1 : PowerSeries ℚ) + (1 + 2 * PowerSeries.X : PowerSeries ℚ) * G + (-PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 3 = 0 := (mul_eq_zero.mp hM).resolve_left (pow_ne_zero 3 hN1)
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A185966Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A185966Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A185966Aux.rel G hP h0c m
      push_cast
      linear_combination r
