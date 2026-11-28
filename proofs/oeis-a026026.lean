import OMAStatements.S_oeis_a026026

-- Problem: A026026: a(n) = number of (s(0), s(1), ..., s(2*n-1)) such that s(i) is a nonnegative integer and |s(i) - s(i-1)| = 1 for i = 1,2,...,n, s(0) = 3, s(2*n-1) = 4. Also a(n) = T(2*n-1,n-1), where T is defined in A026022.
-- Upstream: formal-conjectures statements/oeis-a026026.lean:0 (declaration OMA.S_oeis_a026026.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A026026Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (128 * X ^ 7 + (0) * S) = 64 * X ^ 4 - 448 * X ^ 5 + 960 * X ^ 6 - 640 * X ^ 7 + (-64 * X ^ 4 + 320 * X ^ 5 - 448 * X ^ 6 + 128 * X ^ 7) * S) :
    (-16384 * X + 147456 * X ^ 2 - 442368 * X ^ 3 + 491520 * X ^ 4 - 131072 * X ^ 5) * derivative ℚ G + (-49152 + 327680 * X - 606208 * X ^ 2 + 229376 * X ^ 3 + 65536 * X ^ 4) * G = -81920 * X ^ 2 + 327680 * X ^ 3 - 327680 * X ^ 4 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d320 : derivative ℚ (320 : ℚ⟦X⟧) = 0 := dnum 320
  have d448 : derivative ℚ (448 : ℚ⟦X⟧) = 0 := dnum 448
  have d640 : derivative ℚ (640 : ℚ⟦X⟧) = 0 := dnum 640
  have d960 : derivative ℚ (960 : ℚ⟦X⟧) = 0 := dnum 960
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (128 * X ^ 7) * G = (64 * X ^ 4 - 448 * X ^ 5 + 960 * X ^ 6 - 640 * X ^ 7 : ℚ⟦X⟧) + (-64 * X ^ 4 + 320 * X ^ 5 - 448 * X ^ 6 + 128 * X ^ 7) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((128 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (896 * X ^ 6) * G + (128 * X ^ 7) * derivative ℚ G := by
    simp [Derivation.leibniz, d128]
    ring
  have hR : derivative ℚ ((64 * (X * X * X * X) - 448 * (X * X * X * X * X) + 960 * (X * X * X * X * X * X) - 640 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-64 * (X * X * X * X) + 320 * (X * X * X * X * X) - 448 * (X * X * X * X * X * X) + 128 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * S) =
      256 * X ^ 3 - 2240 * X ^ 4 + 5760 * X ^ 5 - 4480 * X ^ 6 + (-256 * X ^ 3 + 1600 * X ^ 4 - 2688 * X ^ 5 + 896 * X ^ 6) * S + (-64 * X ^ 4 + 320 * X ^ 5 - 448 * X ^ 6 + 128 * X ^ 7) * derivative ℚ S := by
    simp [Derivation.leibniz, d64, d128, d320, d448, d640, d960]
    ring
  have hk2 : (128 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (64 * (X * X * X * X) - 448 * (X * X * X * X * X) + 960 * (X * X * X * X * X * X) - 640 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-64 * (X * X * X * X) + 320 * (X * X * X * X * X) - 448 * (X * X * X * X * X * X) + 128 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (896 * X ^ 6) * G + (128 * X ^ 7) * derivative ℚ G =
      256 * X ^ 3 - 2240 * X ^ 4 + 5760 * X ^ 5 - 4480 * X ^ 6 + (-256 * X ^ 3 + 1600 * X ^ 4 - 2688 * X ^ 5 + 896 * X ^ 6) * S + (-64 * X ^ 4 + 320 * X ^ 5 - 448 * X ^ 6 + 128 * X ^ 7) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 10 * ((-16384 * X + 147456 * X ^ 2 - 442368 * X ^ 3 + 491520 * X ^ 4 - 131072 * X ^ 5) * derivative ℚ G + (-49152 + 327680 * X - 606208 * X ^ 2 + 229376 * X ^ 3 + 65536 * X ^ 4) * G - (-81920 * X ^ 2 + 327680 * X ^ 3 - 327680 * X ^ 4)) = 0 := by
    linear_combination (-64 * X ^ 4 + 320 * X ^ 5 - 448 * X ^ 6 + 128 * X ^ 7) ^ 2 * S * hdS - 2 * (-64 * X ^ 4 + 320 * X ^ 5 - 448 * X ^ 6 + 128 * X ^ 7) ^ 2 * derivative ℚ S * hS -
      (2 * (-256 * X ^ 3 + 1600 * X ^ 4 - 2688 * X ^ 5 + 896 * X ^ 6) * (1 - 4 * X) + (-64 * X ^ 4 + 320 * X ^ 5 - 448 * X ^ 6 + 128 * X ^ 7) * (-4)) * hk + 2 * (-64 * X ^ 4 + 320 * X ^ 5 - 448 * X ^ 6 + 128 * X ^ 7) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 10 ≠ 0 := pow_ne_zero 10 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (128 * X ^ 7 + (0) * S) = 64 * X ^ 4 - 448 * X ^ 5 + 960 * X ^ 6 - 640 * X ^ 7 + (-64 * X ^ 4 + 320 * X ^ 5 - 448 * X ^ 6 + 128 * X ^ 7) * S) :
    (-11 * X ^ 2 + 70 * X ^ 3 - 104 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-6 * X + 38 * X ^ 2 - 20 * X ^ 3) * derivative ℚ G + (114 - 306 * X - 16 * X ^ 2) * G =
      80 * X ^ 2 := by
  have h := key S G hS hG
  have d16384 : derivative ℚ (16384 : ℚ⟦X⟧) = 0 := dnum 16384
  have d49152 : derivative ℚ (49152 : ℚ⟦X⟧) = 0 := dnum 49152
  have d65536 : derivative ℚ (65536 : ℚ⟦X⟧) = 0 := dnum 65536
  have d81920 : derivative ℚ (81920 : ℚ⟦X⟧) = 0 := dnum 81920
  have d131072 : derivative ℚ (131072 : ℚ⟦X⟧) = 0 := dnum 131072
  have d147456 : derivative ℚ (147456 : ℚ⟦X⟧) = 0 := dnum 147456
  have d229376 : derivative ℚ (229376 : ℚ⟦X⟧) = 0 := dnum 229376
  have d327680 : derivative ℚ (327680 : ℚ⟦X⟧) = 0 := dnum 327680
  have d442368 : derivative ℚ (442368 : ℚ⟦X⟧) = 0 := dnum 442368
  have d491520 : derivative ℚ (491520 : ℚ⟦X⟧) = 0 := dnum 491520
  have d606208 : derivative ℚ (606208 : ℚ⟦X⟧) = 0 := dnum 606208
  have hL : derivative ℚ ((-16384 * X + 147456 * (X * X) - 442368 * (X * X * X) + 491520 * (X * X * X * X) - 131072 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-49152 + 327680 * X - 606208 * (X * X) + 229376 * (X * X * X) + 65536 * (X * X * X * X) : ℚ⟦X⟧) * G) =
      (-16384 + 294912 * X - 1327104 * X ^ 2 + 1966080 * X ^ 3 - 655360 * X ^ 4) * derivative ℚ G + (-16384 * X + 147456 * X ^ 2 - 442368 * X ^ 3 + 491520 * X ^ 4 - 131072 * X ^ 5) * derivative ℚ (derivative ℚ G) + (327680 - 1212416 * X + 688128 * X ^ 2 + 262144 * X ^ 3) * G + (-49152 + 327680 * X - 606208 * X ^ 2 + 229376 * X ^ 3 + 65536 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d16384, d49152, d65536, d131072, d147456, d229376, d327680, d442368, d491520, d606208]
    ring
  have hRd : derivative ℚ (-81920 * (X * X) + 327680 * (X * X * X) - 327680 * (X * X * X * X) : ℚ⟦X⟧) = -163840 * X + 983040 * X ^ 2 - 1310720 * X ^ 3 := by
    simp [Derivation.leibniz, d81920, d327680]
    ring
  have h2 : (-16384 * X + 147456 * (X * X) - 442368 * (X * X * X) + 491520 * (X * X * X * X) - 131072 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-49152 + 327680 * X - 606208 * (X * X) + 229376 * (X * X * X) + 65536 * (X * X * X * X) : ℚ⟦X⟧) * G = (-81920 * (X * X) + 327680 * (X * X * X) - 327680 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (-16384 + 294912 * X - 1327104 * X ^ 2 + 1966080 * X ^ 3 - 655360 * X ^ 4) * derivative ℚ G + (-16384 * X + 147456 * X ^ 2 - 442368 * X ^ 3 + 491520 * X ^ 4 - 131072 * X ^ 5) * derivative ℚ (derivative ℚ G) + (327680 - 1212416 * X + 688128 * X ^ 2 + 262144 * X ^ 3) * G + (-49152 + 327680 * X - 606208 * X ^ 2 + 229376 * X ^ 3 + 65536 * X ^ 4) * derivative ℚ G = -163840 * X + 983040 * X ^ 2 - 1310720 * X ^ 3 := by
    rw [← hL, h2, hRd]
  have hfull : (16384 - 81920 * X + 114688 * X ^ 2 - 32768 * X ^ 3) * ((-11 * X ^ 2 + 70 * X ^ 3 - 104 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-6 * X + 38 * X ^ 2 - 20 * X ^ 3) * derivative ℚ G + (114 - 306 * X - 16 * X ^ 2) * G - (80 * X ^ 2)) = 0 := by
    linear_combination (11 * X - 26 * X ^ 2) * hd + (-38 + 112 * X) * h
  have hg : (16384 - 81920 * X + 114688 * X ^ 2 - 32768 * X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (16384 : ℚ⟦X⟧) = 16384 := cnum 16384
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (128 * X ^ 7 + (0) * S) = 64 * X ^ 4 - 448 * X ^ 5 + 960 * X ^ 6 - 640 * X ^ 7 + (-64 * X ^ 4 + 320 * X ^ 5 - 448 * X ^ 6 + 128 * X ^ 7) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C (-11) + derivative ℚ (derivative ℚ G) * X * X * X * C 70 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-104) + derivative ℚ G * X * C (-6) +
      derivative ℚ G * X * X * C 38 + derivative ℚ G * X * X * X * C (-20) +
      G * C 114 + G * X * C (-306) +
      G * X * X * C (-16) =
      C 80 * X * X := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (128 * X ^ 7 + (0) * S) = 64 * X ^ 4 - 448 * X ^ 5 + 960 * X ^ 6 - 640 * X ^ 7 + (-64 * X ^ 4 + 320 * X ^ 5 - 448 * X ^ 6 + 128 * X ^ 7) * S) (m : ℕ) :
    (-11) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 70 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-104) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + (-6) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      38 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-20) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      114 * coeff (m + 1 + 1 + 1 + 1) G + (-306) * coeff (m + 1 + 1 + 1) G +
      (-16) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (128 * X ^ 7 + (0) * S) = 64 * X ^ 4 - 448 * X ^ 5 + 960 * X ^ 6 - 640 * X ^ 7 + (-64 * X ^ 4 + 320 * X ^ 5 - 448 * X ^ 6 + 128 * X ^ 7) * S) :
    (-66) * coeff (0 + 1 + 1 + 1) G + 140 * coeff (0 + 1 + 1) G +
      (-18) * coeff (0 + 1 + 1 + 1) G + 76 * coeff (0 + 1 + 1) G +
      (-20) * coeff (0 + 1) G + 114 * coeff (0 + 1 + 1 + 1) G +
      (-306) * coeff (0 + 1 + 1) G + (-16) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A026026Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026026.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A026026Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (128 * PowerSeries.X ^ 7) * hG - ((-PowerSeries.X ^ 4 - 16 * PowerSeries.X ^ 6) + (6 * PowerSeries.X ^ 4 + 32 * PowerSeries.X ^ 6) * S + (-15 * PowerSeries.X ^ 4 - 16 * PowerSeries.X ^ 6) * S ^ 2 + (20 * PowerSeries.X ^ 4) * S ^ 3 + (-15 * PowerSeries.X ^ 4) * S ^ 4 + (6 * PowerSeries.X ^ 4) * S ^ 5 + (-PowerSeries.X ^ 4) * S ^ 6 + (-2 * PowerSeries.X ^ 5 - 32 * PowerSeries.X ^ 7) * c + (10 * PowerSeries.X ^ 5 + 32 * PowerSeries.X ^ 7) * c * S + (-20 * PowerSeries.X ^ 5) * c * S ^ 2 + (20 * PowerSeries.X ^ 5) * c * S ^ 3 + (-10 * PowerSeries.X ^ 5) * c * S ^ 4 + (2 * PowerSeries.X ^ 5) * c * S ^ 5 + (-4 * PowerSeries.X ^ 6 - 64 * PowerSeries.X ^ 8) * c ^ 2 + (16 * PowerSeries.X ^ 6) * c ^ 2 * S + (-24 * PowerSeries.X ^ 6) * c ^ 2 * S ^ 2 + (16 * PowerSeries.X ^ 6) * c ^ 2 * S ^ 3 + (-4 * PowerSeries.X ^ 6) * c ^ 2 * S ^ 4 + (-8 * PowerSeries.X ^ 7) * c ^ 3 + (24 * PowerSeries.X ^ 7) * c ^ 3 * S + (-24 * PowerSeries.X ^ 7) * c ^ 3 * S ^ 2 + (8 * PowerSeries.X ^ 7) * c ^ 3 * S ^ 3 + (-16 * PowerSeries.X ^ 8) * c ^ 4 + (32 * PowerSeries.X ^ 8) * c ^ 4 * S + (-16 * PowerSeries.X ^ 8) * c ^ 4 * S ^ 2 + (-32 * PowerSeries.X ^ 9) * c ^ 5 + (32 * PowerSeries.X ^ 9) * c ^ 5 * S + (-64 * PowerSeries.X ^ 10) * c ^ 6) * hc - ((-63 * PowerSeries.X ^ 4 + 196 * PowerSeries.X ^ 5 - 160 * PowerSeries.X ^ 6) + (57 * PowerSeries.X ^ 4 - 92 * PowerSeries.X ^ 5 + 32 * PowerSeries.X ^ 6) * S + (-42 * PowerSeries.X ^ 4 + 28 * PowerSeries.X ^ 5) * S ^ 2 + (22 * PowerSeries.X ^ 4 - 4 * PowerSeries.X ^ 5) * S ^ 3 + (-7 * PowerSeries.X ^ 4) * S ^ 4 + (PowerSeries.X ^ 4) * S ^ 5) * hS)
    push_cast
    linear_combination r
  | succ m =>
    have r := A026026Aux.rel (S) G (by linear_combination hS)
        (by linear_combination (128 * PowerSeries.X ^ 7) * hG - ((-PowerSeries.X ^ 4 - 16 * PowerSeries.X ^ 6) + (6 * PowerSeries.X ^ 4 + 32 * PowerSeries.X ^ 6) * S + (-15 * PowerSeries.X ^ 4 - 16 * PowerSeries.X ^ 6) * S ^ 2 + (20 * PowerSeries.X ^ 4) * S ^ 3 + (-15 * PowerSeries.X ^ 4) * S ^ 4 + (6 * PowerSeries.X ^ 4) * S ^ 5 + (-PowerSeries.X ^ 4) * S ^ 6 + (-2 * PowerSeries.X ^ 5 - 32 * PowerSeries.X ^ 7) * c + (10 * PowerSeries.X ^ 5 + 32 * PowerSeries.X ^ 7) * c * S + (-20 * PowerSeries.X ^ 5) * c * S ^ 2 + (20 * PowerSeries.X ^ 5) * c * S ^ 3 + (-10 * PowerSeries.X ^ 5) * c * S ^ 4 + (2 * PowerSeries.X ^ 5) * c * S ^ 5 + (-4 * PowerSeries.X ^ 6 - 64 * PowerSeries.X ^ 8) * c ^ 2 + (16 * PowerSeries.X ^ 6) * c ^ 2 * S + (-24 * PowerSeries.X ^ 6) * c ^ 2 * S ^ 2 + (16 * PowerSeries.X ^ 6) * c ^ 2 * S ^ 3 + (-4 * PowerSeries.X ^ 6) * c ^ 2 * S ^ 4 + (-8 * PowerSeries.X ^ 7) * c ^ 3 + (24 * PowerSeries.X ^ 7) * c ^ 3 * S + (-24 * PowerSeries.X ^ 7) * c ^ 3 * S ^ 2 + (8 * PowerSeries.X ^ 7) * c ^ 3 * S ^ 3 + (-16 * PowerSeries.X ^ 8) * c ^ 4 + (32 * PowerSeries.X ^ 8) * c ^ 4 * S + (-16 * PowerSeries.X ^ 8) * c ^ 4 * S ^ 2 + (-32 * PowerSeries.X ^ 9) * c ^ 5 + (32 * PowerSeries.X ^ 9) * c ^ 5 * S + (-64 * PowerSeries.X ^ 10) * c ^ 6) * hc - ((-63 * PowerSeries.X ^ 4 + 196 * PowerSeries.X ^ 5 - 160 * PowerSeries.X ^ 6) + (57 * PowerSeries.X ^ 4 - 92 * PowerSeries.X ^ 5 + 32 * PowerSeries.X ^ 6) * S + (-42 * PowerSeries.X ^ 4 + 28 * PowerSeries.X ^ 5) * S ^ 2 + (22 * PowerSeries.X ^ 4 - 4 * PowerSeries.X ^ 5) * S ^ 3 + (-7 * PowerSeries.X ^ 4) * S ^ 4 + (PowerSeries.X ^ 4) * S ^ 5) * hS) m
    push_cast
    linear_combination r
