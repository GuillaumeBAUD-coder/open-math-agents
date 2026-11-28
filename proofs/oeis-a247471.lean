import OMAStatements.S_oeis_a247471

-- Problem: A247471: Number of paths in B(n) that start with a u step and end with a d step.
-- Upstream: formal-conjectures statements/oeis-a247471.lean:0 (declaration OMA.S_oeis_a247471.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A247471Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (X ^ 3 - 2 * X ^ 4 - X ^ 5 + 2 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) + (-1 + 3 * X - 3 * X ^ 3 - 2 * X ^ 4 + X ^ 5 + X ^ 6 : ℚ⟦X⟧) * G + (X ^ 3 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (X - 3 * X ^ 2 + X ^ 4 + 4 * X ^ 5 + X ^ 6 - X ^ 7) * derivative ℚ G + (3 - 6 * X - 6 * X ^ 3 - 2 * X ^ 4 - 4 * X ^ 5 + 3 * X ^ 6) * G =
      6 * X ^ 3 - 8 * X ^ 4 - 2 * X ^ 5 - 2 * X ^ 7 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have hp0 : (1 * (X * X * X) - 2 * (X * X * X * X) - 1 * (X * X * X * X * X) + 2 * (X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-1 + 3 * X - 3 * (X * X * X) - 2 * (X * X * X * X) + 1 * (X * X * X * X * X) + 1 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (1 * (X * X * X) : ℚ⟦X⟧) * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 * (X * X * X) - 2 * (X * X * X * X) - 1 * (X * X * X * X * X) + 2 * (X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-1 + 3 * X - 3 * (X * X * X) - 2 * (X * X * X * X) + 1 * (X * X * X * X * X) + 1 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (1 * (X * X * X) : ℚ⟦X⟧) * G * G) =
      (3 * X ^ 2 - 8 * X ^ 3 - 5 * X ^ 4 + 12 * X ^ 5 + 7 * X ^ 6 : ℚ⟦X⟧) + (-1 + 3 * X - 3 * X ^ 3 - 2 * X ^ 4 + X ^ 5 + X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) + (3 - 9 * X ^ 2 - 8 * X ^ 3 + 5 * X ^ 4 + 6 * X ^ 5 : ℚ⟦X⟧) * G + (2 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hd1 : (3 * X ^ 2 - 8 * X ^ 3 - 5 * X ^ 4 + 12 * X ^ 5 + 7 * X ^ 6 : ℚ⟦X⟧) + (-1 + 3 * X - 3 * X ^ 3 - 2 * X ^ 4 + X ^ 5 + X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) + (3 - 9 * X ^ 2 - 8 * X ^ 3 + 5 * X ^ 4 + 6 * X ^ 5 : ℚ⟦X⟧) * G + (2 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 = 0 := by rw [← hL1, hp0, map_zero]
  have hfull : ((-1 + 3 * X - 3 * X ^ 3 - 2 * X ^ 4 + X ^ 5 + X ^ 6 : ℚ⟦X⟧) + (2 * X ^ 3 : ℚ⟦X⟧) * G) ^ 1 * ((X - 3 * X ^ 2 + X ^ 4 + 4 * X ^ 5 + X ^ 6 - X ^ 7) * derivative ℚ G + (3 - 6 * X - 6 * X ^ 3 - 2 * X ^ 4 - 4 * X ^ 5 + 3 * X ^ 6) * G - (6 * X ^ 3 - 8 * X ^ 4 - 2 * X ^ 5 - 2 * X ^ 7)) = 0 := by
    linear_combination ((3 - 3 * X - 15 * X ^ 3 - 16 * X ^ 4 - 11 * X ^ 5 + 9 * X ^ 6 : ℚ⟦X⟧)) * hP +
      ((X - 3 * X ^ 2 + X ^ 4 + 4 * X ^ 5 + X ^ 6 - X ^ 7 : ℚ⟦X⟧)) * hd1
  have hPG : (-1 + 3 * X - 3 * X ^ 3 - 2 * X ^ 4 + X ^ 5 + X ^ 6 : ℚ⟦X⟧) + (2 * X ^ 3 : ℚ⟦X⟧) * G ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 1 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (X ^ 3 - 2 * X ^ 4 - X ^ 5 + 2 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) + (-1 + 3 * X - 3 * X ^ 3 - 2 * X ^ 4 + X ^ 5 + X ^ 6 : ℚ⟦X⟧) * G + (X ^ 3 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ G * X * C 1 + derivative ℚ G * X * X * C (-3) +
      derivative ℚ G * X * X * X * X * C 1 + derivative ℚ G * X * X * X * X * X * C 4 +
      derivative ℚ G * X * X * X * X * X * X * C 1 + derivative ℚ G * X * X * X * X * X * X * X * C (-1) +
      G * C 3 + G * X * C (-6) +
      G * X * X * X * C (-6) + G * X * X * X * X * C (-2) +
      G * X * X * X * X * X * C (-4) + G * X * X * X * X * X * X * C 3 =
      C 6 * X * X * X + C (-8) * X * X * X * X +
      C (-2) * X * X * X * X * X + C (-2) * X * X * X * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (X ^ 3 - 2 * X ^ 4 - X ^ 5 + 2 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) + (-1 + 3 * X - 3 * X ^ 3 - 2 * X ^ 4 + X ^ 5 + X ^ 6 : ℚ⟦X⟧) * G + (X ^ 3 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    1 * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-3) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      1 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 4 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      1 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-1) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      3 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-6) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-4) * coeff (m + 1 + 1 + 1) G + 3 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

end A247471Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a247471.main := by
  intro T G hT hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 8, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 + 1 := rfl
  rw [e1, e3, e4, e5, e6]
  have hN1 : ((1) : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [] at h'
  have hM : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 9) * (((1)) ^ 2 * ((PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 6 + PowerSeries.X ^ 7 : PowerSeries ℚ) + (-1 + 3 * PowerSeries.X - 3 * PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 4 + PowerSeries.X ^ 5 + PowerSeries.X ^ 6 : PowerSeries ℚ) * G + (PowerSeries.X ^ 3 : PowerSeries ℚ) * G ^ 2)) = 0 := by
    linear_combination ((1) * PowerSeries.X ^ 12 + (1) * PowerSeries.X ^ 12 * T + (-2) * PowerSeries.X ^ 13 + (-3) * PowerSeries.X ^ 13 * T + (-1) * PowerSeries.X ^ 14 + (2) * PowerSeries.X ^ 15 + (5) * PowerSeries.X ^ 15 * T + (1) * PowerSeries.X ^ 15 * T ^ 2 + (1) * PowerSeries.X ^ 16 + (-2) * PowerSeries.X ^ 16 * T ^ 2 + (-3) * PowerSeries.X ^ 17 * T + (-1) * PowerSeries.X ^ 17 * T ^ 2 + (-1) * PowerSeries.X ^ 18 * T + (2) * PowerSeries.X ^ 18 * T ^ 2 + (1) * PowerSeries.X ^ 19 * T ^ 2) * hT +
      ((1) * PowerSeries.X ^ 9 + (-3) * PowerSeries.X ^ 10 + (3) * PowerSeries.X ^ 12 + (-1) * PowerSeries.X ^ 12 * G + (2) * PowerSeries.X ^ 13 + (-1) * PowerSeries.X ^ 14 + (-1) * PowerSeries.X ^ 15 + (-1) * PowerSeries.X ^ 15 * T ^ 2 + (1) * PowerSeries.X ^ 16 * T ^ 2 + (1) * PowerSeries.X ^ 17 * T ^ 2) * hG
  have hLne : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 9) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero 9 PowerSeries.X_ne_zero)
  have hP : (PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 6 + PowerSeries.X ^ 7 : PowerSeries ℚ) + (-1 + 3 * PowerSeries.X - 3 * PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 4 + PowerSeries.X ^ 5 + PowerSeries.X ^ 6 : PowerSeries ℚ) * G + (PowerSeries.X ^ 3 : PowerSeries ℚ) * G ^ 2 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 2 hN1)
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    simpa using h
  have r := A247471Aux.rel G hP h0c m
  push_cast
  linear_combination r
