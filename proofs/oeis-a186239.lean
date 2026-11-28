import OMAStatements.S_oeis_a186239

-- Problem: A186239: G.f. A(x) satisfies A(x) = 1+x*A(x)+x^2*A(x)^2+2*x^3*A(x)^3.
-- Upstream: formal-conjectures statements/oeis-a186239.lean:0 (declaration OMA.S_oeis_a186239.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A186239Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * G + (X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (2 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (8 * X ^ 2 + 113 * X ^ 3 - 405 * X ^ 4 - 321 * X ^ 5 - 1411 * X ^ 6) * derivative ℚ (derivative ℚ G) + (28 * X + 248 * X ^ 2 - 1236 * X ^ 3 - 1248 * X ^ 4 - 5644 * X ^ 5) * derivative ℚ G + (12 - 50 * X - 366 * X ^ 2 - 606 * X ^ 3 - 2822 * X ^ 4) * G =
      12 - 10 * X := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have hp0 : (1 : ℚ⟦X⟧) + (-1 + 1 * X : ℚ⟦X⟧) * G + (1 * (X * X) : ℚ⟦X⟧) * G * G + (2 * (X * X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 : ℚ⟦X⟧) + (-1 + 1 * X : ℚ⟦X⟧) * G + (1 * (X * X) : ℚ⟦X⟧) * G * G + (2 * (X * X * X) : ℚ⟦X⟧) * G * G * G) =
      (-1 + X : ℚ⟦X⟧) * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G + (2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G ^ 2 + (6 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (6 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2]
    ring
  have hd1 : (-1 + X : ℚ⟦X⟧) * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G + (2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G ^ 2 + (6 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (6 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-1 + 1 * X : ℚ⟦X⟧) * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G + (2 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G * G + (6 * (X * X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (6 * (X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-1 + 1 * X : ℚ⟦X⟧) * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G + (2 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G * G + (6 * (X * X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (6 * (X * X) : ℚ⟦X⟧) * G * G * G) =
      (-1 + X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (2 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (12 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (2 : ℚ⟦X⟧) * G ^ 2 + (6 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (36 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 * X : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2, d6]
    ring
  have hd2 : (-1 + X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (2 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (12 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (2 : ℚ⟦X⟧) * G ^ 2 + (6 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (36 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 * X : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((-1 + X : ℚ⟦X⟧) + (2 * X ^ 2 : ℚ⟦X⟧) * G + (6 * X ^ 3 : ℚ⟦X⟧) * G ^ 2) ^ 3 * ((8 * X ^ 2 + 113 * X ^ 3 - 405 * X ^ 4 - 321 * X ^ 5 - 1411 * X ^ 6) * derivative ℚ (derivative ℚ G) + (28 * X + 248 * X ^ 2 - 1236 * X ^ 3 - 1248 * X ^ 4 - 5644 * X ^ 5) * derivative ℚ G + (12 - 50 * X - 366 * X ^ 2 - 606 * X ^ 3 - 2822 * X ^ 4) * G - (12 - 10 * X)) = 0 := by
    linear_combination ((12 - 46 * X + 66 * X ^ 2 - 42 * X ^ 3 + 10 * X ^ 4 : ℚ⟦X⟧) + (12 * X ^ 2 + 1260 * X ^ 3 + 1476 * X ^ 4 - 2748 * X ^ 5 : ℚ⟦X⟧) * G + (72 * X ^ 3 + 3672 * X ^ 4 - 8208 * X ^ 5 + 432 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (-5184 * X ^ 6 + 4320 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 + (-7776 * X ^ 7 + 6480 * X ^ 8 : ℚ⟦X⟧) * G ^ 4) * hP +
      ((28 * X + 208 * X ^ 2 - 1494 * X ^ 3 + 436 * X ^ 4 - 4216 * X ^ 5 + 7860 * X ^ 6 - 2822 * X ^ 7 : ℚ⟦X⟧) + (16 * X ^ 4 + 210 * X ^ 5 - 1036 * X ^ 6 + 168 * X ^ 7 - 2180 * X ^ 8 + 2822 * X ^ 9 : ℚ⟦X⟧) * (derivative ℚ G) + (-48 * X ^ 3 - 56 * X ^ 4 + 1566 * X ^ 5 + 1530 * X ^ 6 + 9506 * X ^ 7 - 8466 * X ^ 8 : ℚ⟦X⟧) * G + (96 * X ^ 5 + 1228 * X ^ 6 - 6668 * X ^ 7 + 2628 * X ^ 8 - 11796 * X ^ 9 + 22576 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-48 * X ^ 4 + 1156 * X ^ 5 - 1204 * X ^ 6 + 3084 * X ^ 7 + 12372 * X ^ 8 - 22576 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 + (-288 * X ^ 7 - 4068 * X ^ 8 + 14580 * X ^ 9 + 11556 * X ^ 10 + 50796 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-3540 * X ^ 7 + 4356 * X ^ 8 - 2988 * X ^ 9 - 16932 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 + (-576 * X ^ 8 - 8136 * X ^ 9 + 29160 * X ^ 10 + 23112 * X ^ 11 + 101592 * X ^ 12 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-144 * X ^ 7 - 7344 * X ^ 8 + 13824 * X ^ 9 + 1296 * X ^ 10 : ℚ⟦X⟧) * G ^ 4) * hd1 +
      ((8 * X ^ 2 + 97 * X ^ 3 - 623 * X ^ 4 + 602 * X ^ 5 - 1174 * X ^ 6 + 2501 * X ^ 7 - 1411 * X ^ 8 : ℚ⟦X⟧) + (-32 * X ^ 4 - 420 * X ^ 5 + 2072 * X ^ 6 - 336 * X ^ 7 + 4360 * X ^ 8 - 5644 * X ^ 9 : ℚ⟦X⟧) * G + (-96 * X ^ 5 - 1228 * X ^ 6 + 6668 * X ^ 7 - 2628 * X ^ 8 + 11796 * X ^ 9 - 22576 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 + (192 * X ^ 7 + 2712 * X ^ 8 - 9720 * X ^ 9 - 7704 * X ^ 10 - 33864 * X ^ 11 : ℚ⟦X⟧) * G ^ 3 + (288 * X ^ 8 + 4068 * X ^ 9 - 14580 * X ^ 10 - 11556 * X ^ 11 - 50796 * X ^ 12 : ℚ⟦X⟧) * G ^ 4) * hd2
  have hPG : (-1 + X : ℚ⟦X⟧) + (2 * X ^ 2 : ℚ⟦X⟧) * G + (6 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * G + (X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (2 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C 8 + derivative ℚ (derivative ℚ G) * X * X * X * C 113 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-405) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-321) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-1411) + derivative ℚ G * X * C 28 +
      derivative ℚ G * X * X * C 248 + derivative ℚ G * X * X * X * C (-1236) +
      derivative ℚ G * X * X * X * X * C (-1248) + derivative ℚ G * X * X * X * X * X * C (-5644) +
      G * C 12 + G * X * C (-50) +
      G * X * X * C (-366) + G * X * X * X * C (-606) +
      G * X * X * X * X * C (-2822) =
      C 12 + C (-10) * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * G + (X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (2 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    8 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 113 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-405) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-321) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-1411) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + 28 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      248 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-1236) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-1248) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-5644) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      12 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-50) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-366) * coeff (m + 1 + 1 + 1 + 1) G + (-606) * coeff (m + 1 + 1 + 1) G +
      (-2822) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * G + (X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (2 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    96 * coeff (0 + 1 + 1 + 1 + 1) G + 678 * coeff (0 + 1 + 1 + 1) G +
      (-810) * coeff (0 + 1 + 1) G + 112 * coeff (0 + 1 + 1 + 1 + 1) G +
      744 * coeff (0 + 1 + 1 + 1) G + (-2472) * coeff (0 + 1 + 1) G +
      (-1248) * coeff (0 + 1) G + 12 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-50) * coeff (0 + 1 + 1 + 1) G + (-366) * coeff (0 + 1 + 1) G +
      (-606) * coeff (0 + 1) G + (-2822) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * G + (X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (2 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    160 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 1356 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-2430) * coeff (0 + 1 + 1 + 1) G + (-642) * coeff (0 + 1 + 1) G +
      140 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 992 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-3708) * coeff (0 + 1 + 1 + 1) G + (-2496) * coeff (0 + 1 + 1) G +
      (-5644) * coeff (0 + 1) G + 12 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-50) * coeff (0 + 1 + 1 + 1 + 1) G + (-366) * coeff (0 + 1 + 1 + 1) G +
      (-606) * coeff (0 + 1 + 1) G + (-2822) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A186239Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a186239.main := by
  intro G hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  have hP : (1 : PowerSeries ℚ) + (-1 + PowerSeries.X : PowerSeries ℚ) * G + (PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (2 * PowerSeries.X ^ 3 : PowerSeries ℚ) * G ^ 3 = 0 := by
    linear_combination -hG
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    simpa using h
  cases m with
  | zero =>
    have r := A186239Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A186239Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A186239Aux.rel G hP h0c m
      push_cast
      linear_combination r
