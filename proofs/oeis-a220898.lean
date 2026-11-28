import OMAStatements.S_oeis_a220898

-- Problem: A220898: Number of primitive maps on n edges.
-- Upstream: formal-conjectures statements/oeis-a220898.lean:0 (declaration OMA.S_oeis_a220898.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A220898Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-2 + 23 * X + 25 * X ^ 2 : ℚ⟦X⟧) + (1 - 16 * X - 17 * X ^ 2 : ℚ⟦X⟧) * G + (2 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (2 : ℚ)) :
    (4 * X ^ 2 - 15 * X ^ 3 - 42 * X ^ 4 - 23 * X ^ 5) * derivative ℚ (derivative ℚ G) + (10 * X - 26 * X ^ 2 - 82 * X ^ 3 - 46 * X ^ 4) * derivative ℚ G + (2 - 4 * X) * G =
      4 + 4 * X := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d17 : derivative ℚ (17 : ℚ⟦X⟧) = 0 := dnum 17
  have d23 : derivative ℚ (23 : ℚ⟦X⟧) = 0 := dnum 23
  have d25 : derivative ℚ (25 : ℚ⟦X⟧) = 0 := dnum 25
  have d34 : derivative ℚ (34 : ℚ⟦X⟧) = 0 := dnum 34
  have d50 : derivative ℚ (50 : ℚ⟦X⟧) = 0 := dnum 50
  have hp0 : (-2 + 23 * X + 25 * (X * X) : ℚ⟦X⟧) + (1 - 16 * X - 17 * (X * X) : ℚ⟦X⟧) * G + (2 * X + 2 * (X * X) : ℚ⟦X⟧) * G * G + (1 * (X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-2 + 23 * X + 25 * (X * X) : ℚ⟦X⟧) + (1 - 16 * X - 17 * (X * X) : ℚ⟦X⟧) * G + (2 * X + 2 * (X * X) : ℚ⟦X⟧) * G * G + (1 * (X * X) : ℚ⟦X⟧) * G * G * G) =
      (23 + 50 * X : ℚ⟦X⟧) + (1 - 16 * X - 17 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) + (-16 - 34 * X : ℚ⟦X⟧) * G + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 + 4 * X : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2, d16, d17, d23, d25]
    ring
  have hd1 : (23 + 50 * X : ℚ⟦X⟧) + (1 - 16 * X - 17 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) + (-16 - 34 * X : ℚ⟦X⟧) * G + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 + 4 * X : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (23 + 50 * X : ℚ⟦X⟧) + (1 - 16 * X - 17 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (-16 - 34 * X : ℚ⟦X⟧) * G + (4 * X + 4 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 + 4 * X : ℚ⟦X⟧) * G * G + (3 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((23 + 50 * X : ℚ⟦X⟧) + (1 - 16 * X - 17 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (-16 - 34 * X : ℚ⟦X⟧) * G + (4 * X + 4 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 + 4 * X : ℚ⟦X⟧) * G * G + (3 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G * G * G) =
      (50 : ℚ⟦X⟧) + (1 - 16 * X - 17 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-32 - 68 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-34 : ℚ⟦X⟧) * G + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 + 16 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2, d3, d4, d16, d17, d23, d34, d50]
    ring
  have hd2 : (50 : ℚ⟦X⟧) + (1 - 16 * X - 17 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-32 - 68 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-34 : ℚ⟦X⟧) * G + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 + 16 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((1 - 16 * X - 17 * X ^ 2 : ℚ⟦X⟧) + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2) ^ 3 * ((4 * X ^ 2 - 15 * X ^ 3 - 42 * X ^ 4 - 23 * X ^ 5) * derivative ℚ (derivative ℚ G) + (10 * X - 26 * X ^ 2 - 82 * X ^ 3 - 46 * X ^ 4) * derivative ℚ G + (2 - 4 * X) * G - (4 + 4 * X)) = 0 := by
    linear_combination ((2 + 44 * X - 288 * X ^ 2 - 2838 * X ^ 3 + 4110 * X ^ 4 + 11280 * X ^ 5 + 568 * X ^ 6 - 4094 * X ^ 7 : ℚ⟦X⟧) + (12 * X ^ 2 + 1128 * X ^ 3 - 1518 * X ^ 4 + 3054 * X ^ 5 + 19488 * X ^ 6 + 13800 * X ^ 7 : ℚ⟦X⟧) * G + (-12 * X ^ 2 - 198 * X ^ 3 + 1536 * X ^ 4 - 1074 * X ^ 5 - 7488 * X ^ 6 - 4692 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 + (-16 * X ^ 3 - 256 * X ^ 4 + 336 * X ^ 5 + 944 * X ^ 6 + 368 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 + (-6 * X ^ 4 - 90 * X ^ 5 + 216 * X ^ 6 + 138 * X ^ 7 : ℚ⟦X⟧) * G ^ 4) * hP +
      ((10 * X - 218 * X ^ 2 + 1082 * X ^ 3 + 822 * X ^ 4 + 2338 * X ^ 5 + 16382 * X ^ 6 + 22250 * X ^ 7 + 8694 * X ^ 8 : ℚ⟦X⟧) + (-16 * X ^ 3 + 300 * X ^ 4 - 204 * X ^ 5 - 4136 * X ^ 6 - 7944 * X ^ 7 - 5892 * X ^ 8 - 1564 * X ^ 9 : ℚ⟦X⟧) * (derivative ℚ G) + (48 * X ^ 2 - 584 * X ^ 3 + 440 * X ^ 4 - 350 * X ^ 5 - 14624 * X ^ 6 - 23230 * X ^ 7 - 10028 * X ^ 8 : ℚ⟦X⟧) * G + (-88 * X ^ 4 + 586 * X ^ 5 + 308 * X ^ 6 - 3472 * X ^ 7 - 5084 * X ^ 8 - 1978 * X ^ 9 : ℚ⟦X⟧) * G * (derivative ℚ G) + (76 * X ^ 3 - 192 * X ^ 4 - 664 * X ^ 5 - 80 * X ^ 6 + 684 * X ^ 7 + 368 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 + (-144 * X ^ 5 + 396 * X ^ 6 + 2052 * X ^ 7 + 2340 * X ^ 8 + 828 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (32 * X ^ 4 + 140 * X ^ 5 + 552 * X ^ 6 + 812 * X ^ 7 + 368 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 + (-72 * X ^ 6 + 270 * X ^ 7 + 756 * X ^ 8 + 414 * X ^ 9 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-6 * X ^ 5 + 126 * X ^ 6 + 270 * X ^ 7 + 138 * X ^ 8 : ℚ⟦X⟧) * G ^ 4) * hd1 +
      ((4 * X ^ 2 - 143 * X ^ 3 + 1326 * X ^ 4 + 167 * X ^ 5 - 15592 * X ^ 6 - 32289 * X ^ 7 - 24650 * X ^ 8 - 6647 * X ^ 9 : ℚ⟦X⟧) + (32 * X ^ 3 - 600 * X ^ 4 + 408 * X ^ 5 + 8272 * X ^ 6 + 15888 * X ^ 7 + 11784 * X ^ 8 + 3128 * X ^ 9 : ℚ⟦X⟧) * G + (88 * X ^ 4 - 586 * X ^ 5 - 308 * X ^ 6 + 3472 * X ^ 7 + 5084 * X ^ 8 + 1978 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 + (96 * X ^ 5 - 264 * X ^ 6 - 1368 * X ^ 7 - 1560 * X ^ 8 - 552 * X ^ 9 : ℚ⟦X⟧) * G ^ 3 + (36 * X ^ 6 - 135 * X ^ 7 - 378 * X ^ 8 - 207 * X ^ 9 : ℚ⟦X⟧) * G ^ 4) * hd2
  have hPG : (1 - 16 * X - 17 * X ^ 2 : ℚ⟦X⟧) + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-2 + 23 * X + 25 * X ^ 2 : ℚ⟦X⟧) + (1 - 16 * X - 17 * X ^ 2 : ℚ⟦X⟧) * G + (2 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (2 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C 4 + derivative ℚ (derivative ℚ G) * X * X * X * C (-15) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-42) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-23) +
      derivative ℚ G * X * C 10 + derivative ℚ G * X * X * C (-26) +
      derivative ℚ G * X * X * X * C (-82) + derivative ℚ G * X * X * X * X * C (-46) +
      G * C 2 + G * X * C (-4) =
      C 4 + C 4 * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-2 + 23 * X + 25 * X ^ 2 : ℚ⟦X⟧) + (1 - 16 * X - 17 * X ^ 2 : ℚ⟦X⟧) * G + (2 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (2 : ℚ)) (m : ℕ) :
    4 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-15) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      (-42) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-23) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      10 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-26) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-82) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-46) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      2 * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-4) * coeff (m + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-2 + 23 * X + 25 * X ^ 2 : ℚ⟦X⟧) + (1 - 16 * X - 17 * X ^ 2 : ℚ⟦X⟧) * G + (2 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (2 : ℚ)) :
    24 * coeff (0 + 1 + 1 + 1) G + (-30) * coeff (0 + 1 + 1) G +
      30 * coeff (0 + 1 + 1 + 1) G + (-52) * coeff (0 + 1 + 1) G +
      (-82) * coeff (0 + 1) G + 2 * coeff (0 + 1 + 1 + 1) G +
      (-4) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (-2 + 23 * X + 25 * X ^ 2 : ℚ⟦X⟧) + (1 - 16 * X - 17 * X ^ 2 : ℚ⟦X⟧) * G + (2 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (2 : ℚ)) :
    48 * coeff (0 + 1 + 1 + 1 + 1) G + (-90) * coeff (0 + 1 + 1 + 1) G +
      (-84) * coeff (0 + 1 + 1) G + 40 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-78) * coeff (0 + 1 + 1 + 1) G + (-164) * coeff (0 + 1 + 1) G +
      (-46) * coeff (0 + 1) G + 2 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-4) * coeff (0 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A220898Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a220898.main := by
  intro T G hT hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  have hN1 : ((1) : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [] at h'
  have hM : ((1 : PowerSeries ℚ) * PowerSeries.X ^ 4) * (((1)) ^ 3 * ((-2 + 23 * PowerSeries.X + 25 * PowerSeries.X ^ 2 : PowerSeries ℚ) + (1 - 16 * PowerSeries.X - 17 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G + (2 * PowerSeries.X + 2 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 3)) = 0 := by
    linear_combination ((2) * PowerSeries.X ^ 4 + (-1) * PowerSeries.X ^ 4 * T + (-25) * PowerSeries.X ^ 5 + (26) * PowerSeries.X ^ 5 * T + (-9) * PowerSeries.X ^ 5 * T ^ 2 + (1) * PowerSeries.X ^ 5 * T ^ 3) * hT +
      ((1) * PowerSeries.X ^ 4 + (-16) * PowerSeries.X ^ 5 + (6) * PowerSeries.X ^ 5 * T + (-2) * PowerSeries.X ^ 5 * T ^ 2 + (2) * PowerSeries.X ^ 5 * G + (-17) * PowerSeries.X ^ 6 + (6) * PowerSeries.X ^ 6 * T + (7) * PowerSeries.X ^ 6 * T ^ 2 + (-6) * PowerSeries.X ^ 6 * T ^ 3 + (1) * PowerSeries.X ^ 6 * T ^ 4 + (2) * PowerSeries.X ^ 6 * G + (3) * PowerSeries.X ^ 6 * G * T + (-1) * PowerSeries.X ^ 6 * G * T ^ 2 + (1) * PowerSeries.X ^ 6 * G ^ 2) * hG
  have hLne : ((1 : PowerSeries ℚ) * PowerSeries.X ^ 4) ≠ 0 := mul_ne_zero one_ne_zero (pow_ne_zero 4 PowerSeries.X_ne_zero)
  have hP : (-2 + 23 * PowerSeries.X + 25 * PowerSeries.X ^ 2 : PowerSeries ℚ) + (1 - 16 * PowerSeries.X - 17 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G + (2 * PowerSeries.X + 2 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 3 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 3 hN1)
  have h0c : PowerSeries.constantCoeff G = (2 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A220898Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A220898Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A220898Aux.rel G hP h0c m
      push_cast
      linear_combination r
