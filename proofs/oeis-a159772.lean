import OMAStatements.S_oeis_a159772

-- Problem: A159772: Number of n-leaf binary trees that do not contain (()((((()())())())())) as a subtree.
-- Upstream: formal-conjectures statements/oeis-a159772.lean:0 (declaration OMA.S_oeis_a159772.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A159772Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-X ^ 4 : ℚ⟦X⟧) + (4 * X ^ 3 : ℚ⟦X⟧) * G + (X - 6 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 = 0) :
    (4 * X ^ 2 - 43 * X ^ 3 + 176 * X ^ 4 - 344 * X ^ 5 + 288 * X ^ 6 - 128 * X ^ 7 + 512 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-6 * X + 43 * X ^ 2 - 184 * X ^ 3 + 456 * X ^ 4 - 192 * X ^ 5 - 128 * X ^ 6) * derivative ℚ G + (6 - 48 * X + 220 * X ^ 2 - 432 * X ^ 3 + 96 * X ^ 4 + 128 * X ^ 5) * G =
      -3 * X ^ 2 + 12 * X ^ 3 + 24 * X ^ 4 - 32 * X ^ 5 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have hp0 : (-1 * (X * X * X * X) : ℚ⟦X⟧) + (4 * (X * X * X) : ℚ⟦X⟧) * G + (1 * X - 6 * (X * X) : ℚ⟦X⟧) * G * G + (-1 + 4 * X : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 * (X * X * X * X) : ℚ⟦X⟧) + (4 * (X * X * X) : ℚ⟦X⟧) * G + (1 * X - 6 * (X * X) : ℚ⟦X⟧) * G * G + (-1 + 4 * X : ℚ⟦X⟧) * G * G * G) =
      (-4 * X ^ 3 : ℚ⟦X⟧) + (4 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ G) + (12 * X ^ 2 : ℚ⟦X⟧) * G + (2 * X - 12 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 - 12 * X : ℚ⟦X⟧) * G ^ 2 + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d4, d6]
    ring
  have hd1 : (-4 * X ^ 3 : ℚ⟦X⟧) + (4 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ G) + (12 * X ^ 2 : ℚ⟦X⟧) * G + (2 * X - 12 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 - 12 * X : ℚ⟦X⟧) * G ^ 2 + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-4 * (X * X * X) : ℚ⟦X⟧) + (4 * (X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (12 * (X * X) : ℚ⟦X⟧) * G + (2 * X - 12 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 - 12 * X : ℚ⟦X⟧) * G * G + (-3 + 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-4 * (X * X * X) : ℚ⟦X⟧) + (4 * (X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (12 * (X * X) : ℚ⟦X⟧) * G + (2 * X - 12 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 - 12 * X : ℚ⟦X⟧) * G * G + (-3 + 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G) =
      (-12 * X ^ 2 : ℚ⟦X⟧) + (4 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (24 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X - 12 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (24 * X : ℚ⟦X⟧) * G + (2 * X - 12 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (4 - 48 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 + 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-12 : ℚ⟦X⟧) * G ^ 2 + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d2, d3, d4, d12]
    ring
  have hd2 : (-12 * X ^ 2 : ℚ⟦X⟧) + (4 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (24 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X - 12 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (24 * X : ℚ⟦X⟧) * G + (2 * X - 12 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (4 - 48 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 + 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-12 : ℚ⟦X⟧) * G ^ 2 + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((4 * X ^ 3 : ℚ⟦X⟧) + (2 * X - 12 * X ^ 2 : ℚ⟦X⟧) * G + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2) ^ 3 * ((4 * X ^ 2 - 43 * X ^ 3 + 176 * X ^ 4 - 344 * X ^ 5 + 288 * X ^ 6 - 128 * X ^ 7 + 512 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-6 * X + 43 * X ^ 2 - 184 * X ^ 3 + 456 * X ^ 4 - 192 * X ^ 5 - 128 * X ^ 6) * derivative ℚ G + (6 - 48 * X + 220 * X ^ 2 - 432 * X ^ 3 + 96 * X ^ 4 + 128 * X ^ 5) * G - (-3 * X ^ 2 + 12 * X ^ 3 + 24 * X ^ 4 - 32 * X ^ 5)) = 0 := by
    linear_combination ((128 * X ^ 5 - 992 * X ^ 6 + 2688 * X ^ 7 + 1536 * X ^ 8 - 18432 * X ^ 9 + 6144 * X ^ 10 + 24576 * X ^ 11 : ℚ⟦X⟧) + (-1216 * X ^ 5 + 13824 * X ^ 6 - 70656 * X ^ 7 + 147456 * X ^ 8 - 36864 * X ^ 9 - 98304 * X ^ 10 : ℚ⟦X⟧) * G + (96 * X ^ 2 - 2080 * X ^ 3 + 18912 * X ^ 4 - 99072 * X ^ 5 + 313344 * X ^ 6 - 485376 * X ^ 7 + 141312 * X ^ 8 + 147456 * X ^ 9 + 98304 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 + (-216 * X + 4176 * X ^ 2 - 35200 * X ^ 3 + 170496 * X ^ 4 - 482816 * X ^ 5 + 666624 * X ^ 6 - 196608 * X ^ 7 - 114688 * X ^ 8 - 196608 * X ^ 9 : ℚ⟦X⟧) * G ^ 3 + (162 - 2808 * X + 22080 * X ^ 2 - 100992 * X ^ 3 + 267648 * X ^ 4 - 342528 * X ^ 5 + 92160 * X ^ 6 + 49152 * X ^ 7 + 98304 * X ^ 8 : ℚ⟦X⟧) * G ^ 4) * hP +
      ((-32 * X ^ 6 + 56 * X ^ 7 + 1344 * X ^ 8 - 8640 * X ^ 9 + 21504 * X ^ 10 - 15872 * X ^ 11 - 24576 * X ^ 13 : ℚ⟦X⟧) + (-32 * X ^ 6 + 536 * X ^ 7 - 3472 * X ^ 8 + 11200 * X ^ 9 - 18816 * X ^ 10 + 14848 * X ^ 11 - 10240 * X ^ 12 + 24576 * X ^ 13 : ℚ⟦X⟧) * (derivative ℚ G) + (-160 * X ^ 5 + 2912 * X ^ 6 - 20208 * X ^ 7 + 72704 * X ^ 8 - 134016 * X ^ 9 + 87552 * X ^ 10 - 26624 * X ^ 11 + 122880 * X ^ 12 : ℚ⟦X⟧) * G + (-16 * X ^ 4 + 460 * X ^ 5 - 4760 * X ^ 6 + 24368 * X ^ 7 - 68160 * X ^ 8 + 103808 * X ^ 9 - 80384 * X ^ 10 + 67584 * X ^ 11 - 122880 * X ^ 12 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-48 * X ^ 3 + 1294 * X ^ 4 - 13084 * X ^ 5 + 69168 * X ^ 6 - 209568 * X ^ 7 + 336256 * X ^ 8 - 205824 * X ^ 9 + 92160 * X ^ 10 - 270336 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 + (72 * X ^ 3 - 1494 * X ^ 4 + 12636 * X ^ 5 - 56448 * X ^ 6 + 143136 * X ^ 7 - 202752 * X ^ 8 + 156672 * X ^ 9 - 147456 * X ^ 10 + 221184 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (96 * X ^ 2 - 2038 * X ^ 3 + 18112 * X ^ 4 - 88640 * X ^ 5 + 251456 * X ^ 6 - 374400 * X ^ 7 + 212480 * X ^ 8 - 100352 * X ^ 9 + 270336 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 + (-72 * X ^ 2 + 1350 * X ^ 3 - 10512 * X ^ 4 + 43920 * X ^ 5 - 105408 * X ^ 6 + 142848 * X ^ 7 - 110592 * X ^ 8 + 110592 * X ^ 9 - 147456 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-54 * X + 1011 * X ^ 2 - 8448 * X ^ 3 + 40248 * X ^ 4 - 111360 * X ^ 5 + 158208 * X ^ 6 - 79872 * X ^ 7 + 30720 * X ^ 8 - 98304 * X ^ 9 : ℚ⟦X⟧) * G ^ 4) * hd1 +
      ((64 * X ^ 8 - 688 * X ^ 9 + 2816 * X ^ 10 - 5504 * X ^ 11 + 4608 * X ^ 12 - 2048 * X ^ 13 + 8192 * X ^ 14 : ℚ⟦X⟧) + (64 * X ^ 6 - 1072 * X ^ 7 + 6944 * X ^ 8 - 22400 * X ^ 9 + 37632 * X ^ 10 - 29696 * X ^ 11 + 20480 * X ^ 12 - 49152 * X ^ 13 : ℚ⟦X⟧) * G + (16 * X ^ 4 - 460 * X ^ 5 + 4760 * X ^ 6 - 24368 * X ^ 7 + 68160 * X ^ 8 - 103808 * X ^ 9 + 80384 * X ^ 10 - 67584 * X ^ 11 + 122880 * X ^ 12 : ℚ⟦X⟧) * G ^ 2 + (-48 * X ^ 3 + 996 * X ^ 4 - 8424 * X ^ 5 + 37632 * X ^ 6 - 95424 * X ^ 7 + 135168 * X ^ 8 - 104448 * X ^ 9 + 98304 * X ^ 10 - 147456 * X ^ 11 : ℚ⟦X⟧) * G ^ 3 + (36 * X ^ 2 - 675 * X ^ 3 + 5256 * X ^ 4 - 21960 * X ^ 5 + 52704 * X ^ 6 - 71424 * X ^ 7 + 55296 * X ^ 8 - 55296 * X ^ 9 + 73728 * X ^ 10 : ℚ⟦X⟧) * G ^ 4) * hd2
  have hres : ((-4032 * X ^ 3 + 8064 * X ^ 4 + 23040 * X ^ 5 : ℚ⟦X⟧) + (-1152 * X + 9792 * X ^ 2 - 4608 * X ^ 3 - 55296 * X ^ 4 : ℚ⟦X⟧) * G + (1152 - 4608 * X - 13824 * X ^ 2 + 55296 * X ^ 3 : ℚ⟦X⟧) * G ^ 2) * ((4 * X ^ 3 : ℚ⟦X⟧) + (2 * X - 12 * X ^ 2 : ℚ⟦X⟧) * G + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2) = (-2304 * X ^ 5 + 6336 * X ^ 6 + 4608 * X ^ 7 + 9216 * X ^ 8 : ℚ⟦X⟧) := by
    linear_combination (-((2304 * X - 22464 * X ^ 2 + 27648 * X ^ 3 + 82944 * X ^ 4 : ℚ⟦X⟧) + (-3456 + 13824 * X + 41472 * X ^ 2 - 165888 * X ^ 3 : ℚ⟦X⟧) * G)) * hP
  have hd0 : (-2304 + 6336 * X + 4608 * X ^ 2 + 9216 * X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    have kc : constantCoeff (2304 : ℚ⟦X⟧) = 2304 := cnum 2304
    simp [kc] at h'
  have hdisc : (-2304 * X ^ 5 + 6336 * X ^ 6 + 4608 * X ^ 7 + 9216 * X ^ 8 : ℚ⟦X⟧) ≠ 0 := by
    have e : (-2304 * X ^ 5 + 6336 * X ^ 6 + 4608 * X ^ 7 + 9216 * X ^ 8 : ℚ⟦X⟧) = X ^ 5 * (-2304 + 6336 * X + 4608 * X ^ 2 + 9216 * X ^ 3 : ℚ⟦X⟧) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 5 X_ne_zero) hd0
  have hPG : (4 * X ^ 3 : ℚ⟦X⟧) + (2 * X - 12 * X ^ 2 : ℚ⟦X⟧) * G + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hres
    exact hdisc hres.symm
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-X ^ 4 : ℚ⟦X⟧) + (4 * X ^ 3 : ℚ⟦X⟧) * G + (X - 6 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 = 0) :
    derivative ℚ (derivative ℚ G) * X * X * C 4 + derivative ℚ (derivative ℚ G) * X * X * X * C (-43) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 176 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-344) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 288 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C (-128) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * C 512 + derivative ℚ G * X * C (-6) +
      derivative ℚ G * X * X * C 43 + derivative ℚ G * X * X * X * C (-184) +
      derivative ℚ G * X * X * X * X * C 456 + derivative ℚ G * X * X * X * X * X * C (-192) +
      derivative ℚ G * X * X * X * X * X * X * C (-128) + G * C 6 +
      G * X * C (-48) + G * X * X * C 220 +
      G * X * X * X * C (-432) + G * X * X * X * X * C 96 +
      G * X * X * X * X * X * C 128 =
      C (-3) * X * X + C 12 * X * X * X +
      C 24 * X * X * X * X + C (-32) * X * X * X * X * X := by
  have h := key G hP
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-X ^ 4 : ℚ⟦X⟧) + (4 * X ^ 3 : ℚ⟦X⟧) * G + (X - 6 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 = 0) (m : ℕ) :
    4 * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-43) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      176 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-344) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      288 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-128) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      512 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + (-6) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      43 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-184) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      456 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-192) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-128) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 6 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-48) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 220 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-432) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 96 * coeff (m + 1 + 1 + 1 + 1) G +
      128 * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-X ^ 4 : ℚ⟦X⟧) + (4 * X ^ 3 : ℚ⟦X⟧) * G + (X - 6 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 = 0) :
    120 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-860) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      2112 * coeff (0 + 1 + 1 + 1 + 1) G + (-2064) * coeff (0 + 1 + 1 + 1) G +
      576 * coeff (0 + 1 + 1) G + (-36) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      215 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-736) * coeff (0 + 1 + 1 + 1 + 1) G +
      1368 * coeff (0 + 1 + 1 + 1) G + (-384) * coeff (0 + 1 + 1) G +
      (-128) * coeff (0 + 1) G + 6 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-48) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 220 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-432) * coeff (0 + 1 + 1 + 1) G + 96 * coeff (0 + 1 + 1) G +
      128 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (-X ^ 4 : ℚ⟦X⟧) + (4 * X ^ 3 : ℚ⟦X⟧) * G + (X - 6 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 = 0) :
    168 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1290) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      3520 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-4128) * coeff (0 + 1 + 1 + 1 + 1) G +
      1728 * coeff (0 + 1 + 1 + 1) G + (-256) * coeff (0 + 1 + 1) G +
      (-42) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 258 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-920) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 1824 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-576) * coeff (0 + 1 + 1 + 1) G + (-256) * coeff (0 + 1 + 1) G +
      6 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-48) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      220 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-432) * coeff (0 + 1 + 1 + 1 + 1) G +
      96 * coeff (0 + 1 + 1 + 1) G + 128 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A159772Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a159772.main := by
  intro T G hT hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 6, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m := rfl
  rw [e1, e2, e3, e4, e5, e6]
  have hN1 : ((1) + (-1) * PowerSeries.X * T : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [] at h'
  have hM : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 3) * (((1) + (-1) * PowerSeries.X * T) ^ 3 * ((-PowerSeries.X ^ 4 : PowerSeries ℚ) + (4 * PowerSeries.X ^ 3 : PowerSeries ℚ) * G + (PowerSeries.X - 6 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (-1 + 4 * PowerSeries.X : PowerSeries ℚ) * G ^ 3)) = 0 := by
    linear_combination ((1) * PowerSeries.X ^ 7) * hT +
      ((1) * PowerSeries.X ^ 3 * G ^ 2 + (-4) * PowerSeries.X ^ 4 * G ^ 2 + (-2) * PowerSeries.X ^ 4 * G ^ 2 * T + (2) * PowerSeries.X ^ 5 * G + (1) * PowerSeries.X ^ 5 * G * T + (8) * PowerSeries.X ^ 5 * G ^ 2 * T + (1) * PowerSeries.X ^ 5 * G ^ 2 * T ^ 2 + (-2) * PowerSeries.X ^ 6 + (1) * PowerSeries.X ^ 6 * T + (-8) * PowerSeries.X ^ 6 * G * T + (-1) * PowerSeries.X ^ 6 * G * T ^ 2 + (-4) * PowerSeries.X ^ 6 * G ^ 2 * T ^ 2 + (2) * PowerSeries.X ^ 7 * T + (6) * PowerSeries.X ^ 7 * G * T ^ 2 + (-4) * PowerSeries.X ^ 8 * T ^ 2) * hG
  have hLne : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 3) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero 3 PowerSeries.X_ne_zero)
  have hP : (-PowerSeries.X ^ 4 : PowerSeries ℚ) + (4 * PowerSeries.X ^ 3 : PowerSeries ℚ) * G + (PowerSeries.X - 6 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (-1 + 4 * PowerSeries.X : PowerSeries ℚ) * G ^ 3 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 3 hN1)
  cases m with
  | zero =>
    have r := A159772Aux.relE0 G hP
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A159772Aux.relE1 G hP
      push_cast
      linear_combination r
    | succ m =>
      have r := A159772Aux.rel G hP m
      push_cast
      linear_combination r
