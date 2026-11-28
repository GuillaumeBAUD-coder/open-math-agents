import OMAStatements.S_oeis_a026672

-- Problem: A026672: a(n) = T(2n,n-1), T given by A026670. Also T(2n,n-1)=T(2n+1,n+2), T given by A026725; and T(2n,n-1), T given by A026736.
-- Upstream: formal-conjectures statements/oeis-a026672.lean:0 (declaration OMA.S_oeis_a026672.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A026672Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-8 * X ^ 2 + 24 * X ^ 3 + 16 * X ^ 4 + (8 * X ^ 2 - 8 * X ^ 3) * S) = 8 * X - 32 * X ^ 2 + 16 * X ^ 3 + (-8 * X + 16 * X ^ 2) * S) :
    (65536 * X - 720896 * X ^ 2 + 2555904 * X ^ 3 - 2686976 * X ^ 4 - 786432 * X ^ 5) * derivative ℚ G + (65536 - 655360 * X + 1769472 * X ^ 2 - 524288 * X ^ 3 - 1179648 * X ^ 4) * G = 131072 * X - 393216 * X ^ 2 - 393216 * X ^ 3 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have d384 : derivative ℚ (384 : ℚ⟦X⟧) = 0 := dnum 384
  have d640 : derivative ℚ (640 : ℚ⟦X⟧) = 0 := dnum 640
  have d1024 : derivative ℚ (1024 : ℚ⟦X⟧) = 0 := dnum 1024
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-256 * X ^ 6 + 1024 * X ^ 7 + 256 * X ^ 8) * G = (128 * X ^ 5 - 640 * X ^ 6 + 256 * X ^ 7 : ℚ⟦X⟧) + (-128 * X ^ 5 + 384 * X ^ 6) * S := by
    linear_combination (-8 * X ^ 2 + 24 * X ^ 3 + 16 * X ^ 4 - (8 * X ^ 2 - 8 * X ^ 3) * S) * hG + (8 * X ^ 2 - 8 * X ^ 3) * ((8 * X ^ 2 - 8 * X ^ 3) * G - (-8 * X + 16 * X ^ 2)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-256 * (X * X * X * X * X * X) + 1024 * (X * X * X * X * X * X * X) + 256 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-1536 * X ^ 5 + 7168 * X ^ 6 + 2048 * X ^ 7) * G + (-256 * X ^ 6 + 1024 * X ^ 7 + 256 * X ^ 8) * derivative ℚ G := by
    simp [Derivation.leibniz, d256, d1024]
    ring
  have hR : derivative ℚ ((128 * (X * X * X * X * X) - 640 * (X * X * X * X * X * X) + 256 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-128 * (X * X * X * X * X) + 384 * (X * X * X * X * X * X) : ℚ⟦X⟧) * S) =
      640 * X ^ 4 - 3840 * X ^ 5 + 1792 * X ^ 6 + (-640 * X ^ 4 + 2304 * X ^ 5) * S + (-128 * X ^ 5 + 384 * X ^ 6) * derivative ℚ S := by
    simp [Derivation.leibniz, d128, d256, d384, d640]
    ring
  have hk2 : (-256 * (X * X * X * X * X * X) + 1024 * (X * X * X * X * X * X * X) + 256 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (128 * (X * X * X * X * X) - 640 * (X * X * X * X * X * X) + 256 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-128 * (X * X * X * X * X) + 384 * (X * X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-1536 * X ^ 5 + 7168 * X ^ 6 + 2048 * X ^ 7) * G + (-256 * X ^ 6 + 1024 * X ^ 7 + 256 * X ^ 8) * derivative ℚ G =
      640 * X ^ 4 - 3840 * X ^ 5 + 1792 * X ^ 6 + (-640 * X ^ 4 + 2304 * X ^ 5) * S + (-128 * X ^ 5 + 384 * X ^ 6) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 10 * ((65536 * X - 720896 * X ^ 2 + 2555904 * X ^ 3 - 2686976 * X ^ 4 - 786432 * X ^ 5) * derivative ℚ G + (65536 - 655360 * X + 1769472 * X ^ 2 - 524288 * X ^ 3 - 1179648 * X ^ 4) * G - (131072 * X - 393216 * X ^ 2 - 393216 * X ^ 3)) = 0 := by
    linear_combination (-128 * X ^ 5 + 384 * X ^ 6) ^ 2 * S * hdS - 2 * (-128 * X ^ 5 + 384 * X ^ 6) ^ 2 * derivative ℚ S * hS -
      (2 * (-640 * X ^ 4 + 2304 * X ^ 5) * (1 - 4 * X) + (-128 * X ^ 5 + 384 * X ^ 6) * (-4)) * hk + 2 * (-128 * X ^ 5 + 384 * X ^ 6) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 10 ≠ 0 := pow_ne_zero 10 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-8 * X ^ 2 + 24 * X ^ 3 + 16 * X ^ 4 + (8 * X ^ 2 - 8 * X ^ 3) * S) = 8 * X - 32 * X ^ 2 + 16 * X ^ 3 + (-8 * X + 16 * X ^ 2) * S) :
    (-X ^ 2 + 8 * X ^ 3 - 15 * X ^ 4 - 4 * X ^ 5) * derivative ℚ (derivative ℚ G) + (4 * X - 22 * X ^ 2 + 24 * X ^ 3 - 2 * X ^ 4) * derivative ℚ G + (6 - 32 * X + 12 * X ^ 2 + 12 * X ^ 3) * G =
      10 * X + 6 * X ^ 2 := by
  have h := key S G hS hG
  have d65536 : derivative ℚ (65536 : ℚ⟦X⟧) = 0 := dnum 65536
  have d131072 : derivative ℚ (131072 : ℚ⟦X⟧) = 0 := dnum 131072
  have d393216 : derivative ℚ (393216 : ℚ⟦X⟧) = 0 := dnum 393216
  have d524288 : derivative ℚ (524288 : ℚ⟦X⟧) = 0 := dnum 524288
  have d655360 : derivative ℚ (655360 : ℚ⟦X⟧) = 0 := dnum 655360
  have d720896 : derivative ℚ (720896 : ℚ⟦X⟧) = 0 := dnum 720896
  have d786432 : derivative ℚ (786432 : ℚ⟦X⟧) = 0 := dnum 786432
  have d1179648 : derivative ℚ (1179648 : ℚ⟦X⟧) = 0 := dnum 1179648
  have d1769472 : derivative ℚ (1769472 : ℚ⟦X⟧) = 0 := dnum 1769472
  have d2555904 : derivative ℚ (2555904 : ℚ⟦X⟧) = 0 := dnum 2555904
  have d2686976 : derivative ℚ (2686976 : ℚ⟦X⟧) = 0 := dnum 2686976
  have hL : derivative ℚ ((65536 * X - 720896 * (X * X) + 2555904 * (X * X * X) - 2686976 * (X * X * X * X) - 786432 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (65536 - 655360 * X + 1769472 * (X * X) - 524288 * (X * X * X) - 1179648 * (X * X * X * X) : ℚ⟦X⟧) * G) =
      (65536 - 1441792 * X + 7667712 * X ^ 2 - 10747904 * X ^ 3 - 3932160 * X ^ 4) * derivative ℚ G + (65536 * X - 720896 * X ^ 2 + 2555904 * X ^ 3 - 2686976 * X ^ 4 - 786432 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-655360 + 3538944 * X - 1572864 * X ^ 2 - 4718592 * X ^ 3) * G + (65536 - 655360 * X + 1769472 * X ^ 2 - 524288 * X ^ 3 - 1179648 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d65536, d524288, d655360, d720896, d786432, d1179648, d1769472, d2555904, d2686976]
    ring
  have hRd : derivative ℚ (131072 * X - 393216 * (X * X) - 393216 * (X * X * X) : ℚ⟦X⟧) = 131072 - 786432 * X - 1179648 * X ^ 2 := by
    simp [Derivation.leibniz, d131072, d393216]
    ring
  have h2 : (65536 * X - 720896 * (X * X) + 2555904 * (X * X * X) - 2686976 * (X * X * X * X) - 786432 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (65536 - 655360 * X + 1769472 * (X * X) - 524288 * (X * X * X) - 1179648 * (X * X * X * X) : ℚ⟦X⟧) * G = (131072 * X - 393216 * (X * X) - 393216 * (X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (65536 - 1441792 * X + 7667712 * X ^ 2 - 10747904 * X ^ 3 - 3932160 * X ^ 4) * derivative ℚ G + (65536 * X - 720896 * X ^ 2 + 2555904 * X ^ 3 - 2686976 * X ^ 4 - 786432 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-655360 + 3538944 * X - 1572864 * X ^ 2 - 4718592 * X ^ 3) * G + (65536 - 655360 * X + 1769472 * X ^ 2 - 524288 * X ^ 3 - 1179648 * X ^ 4) * derivative ℚ G = 131072 - 786432 * X - 1179648 * X ^ 2 := by
    rw [← hL, h2, hRd]
  have hfull : (65536 - 196608 * X) * ((-X ^ 2 + 8 * X ^ 3 - 15 * X ^ 4 - 4 * X ^ 5) * derivative ℚ (derivative ℚ G) + (4 * X - 22 * X ^ 2 + 24 * X ^ 3 - 2 * X ^ 4) * derivative ℚ G + (6 - 32 * X + 12 * X ^ 2 + 12 * X ^ 3) * G - (10 * X + 6 * X ^ 2)) = 0 := by
    linear_combination (-X) * hd + (6) * h
  have hg : (65536 - 196608 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (65536 : ℚ⟦X⟧) = 65536 := cnum 65536
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-8 * X ^ 2 + 24 * X ^ 3 + 16 * X ^ 4 + (8 * X ^ 2 - 8 * X ^ 3) * S) = 8 * X - 32 * X ^ 2 + 16 * X ^ 3 + (-8 * X + 16 * X ^ 2) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C (-1) + derivative ℚ (derivative ℚ G) * X * X * X * C 8 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-15) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-4) +
      derivative ℚ G * X * C 4 + derivative ℚ G * X * X * C (-22) +
      derivative ℚ G * X * X * X * C 24 + derivative ℚ G * X * X * X * X * C (-2) +
      G * C 6 + G * X * C (-32) +
      G * X * X * C 12 + G * X * X * X * C 12 =
      C 10 * X + C 6 * X * X := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-8 * X ^ 2 + 24 * X ^ 3 + 16 * X ^ 4 + (8 * X ^ 2 - 8 * X ^ 3) * S) = 8 * X - 32 * X ^ 2 + 16 * X ^ 3 + (-8 * X + 16 * X ^ 2) * S) (m : ℕ) :
    (-1) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 8 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      (-15) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-4) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      4 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-22) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      24 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-2) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      6 * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-32) * coeff (m + 1 + 1 + 1 + 1) G +
      12 * coeff (m + 1 + 1 + 1) G + 12 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-8 * X ^ 2 + 24 * X ^ 3 + 16 * X ^ 4 + (8 * X ^ 2 - 8 * X ^ 3) * S) = 8 * X - 32 * X ^ 2 + 16 * X ^ 3 + (-8 * X + 16 * X ^ 2) * S) :
    (-6) * coeff (0 + 1 + 1 + 1) G + 16 * coeff (0 + 1 + 1) G +
      12 * coeff (0 + 1 + 1 + 1) G + (-44) * coeff (0 + 1 + 1) G +
      24 * coeff (0 + 1) G + 6 * coeff (0 + 1 + 1 + 1) G +
      (-32) * coeff (0 + 1 + 1) G + 12 * coeff (0 + 1) G +
      12 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-8 * X ^ 2 + 24 * X ^ 3 + 16 * X ^ 4 + (8 * X ^ 2 - 8 * X ^ 3) * S) = 8 * X - 32 * X ^ 2 + 16 * X ^ 3 + (-8 * X + 16 * X ^ 2) * S) :
    (-12) * coeff (0 + 1 + 1 + 1 + 1) G + 48 * coeff (0 + 1 + 1 + 1) G +
      (-30) * coeff (0 + 1 + 1) G + 16 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-66) * coeff (0 + 1 + 1 + 1) G + 48 * coeff (0 + 1 + 1) G +
      (-2) * coeff (0 + 1) G + 6 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-32) * coeff (0 + 1 + 1 + 1) G + 12 * coeff (0 + 1 + 1) G +
      12 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A026672Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026672.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  cases m with
  | zero =>
    have r := A026672Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (16 * PowerSeries.X ^ 4) * hG - ((-PowerSeries.X) + (-2 * PowerSeries.X ^ 2) * G + (3 * PowerSeries.X) * S + (4 * PowerSeries.X ^ 2) * S * G + (-3 * PowerSeries.X) * S ^ 2 + (-2 * PowerSeries.X ^ 2) * S ^ 2 * G + (PowerSeries.X) * S ^ 3 + (-2 * PowerSeries.X ^ 2) * c + (-4 * PowerSeries.X ^ 3) * c * G + (4 * PowerSeries.X ^ 2) * c * S + (4 * PowerSeries.X ^ 3) * c * S * G + (-2 * PowerSeries.X ^ 2) * c * S ^ 2 + (-4 * PowerSeries.X ^ 3) * c ^ 2 + (-8 * PowerSeries.X ^ 4) * c ^ 2 * G + (4 * PowerSeries.X ^ 3) * c ^ 2 * S + (-8 * PowerSeries.X ^ 4) * c ^ 3) * hc - ((-7 * PowerSeries.X + 4 * PowerSeries.X ^ 2) + (-6 * PowerSeries.X ^ 2) * G + (4 * PowerSeries.X) * S + (2 * PowerSeries.X ^ 2) * S * G + (-PowerSeries.X) * S ^ 2) * hS)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A026672Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination (16 * PowerSeries.X ^ 4) * hG - ((-PowerSeries.X) + (-2 * PowerSeries.X ^ 2) * G + (3 * PowerSeries.X) * S + (4 * PowerSeries.X ^ 2) * S * G + (-3 * PowerSeries.X) * S ^ 2 + (-2 * PowerSeries.X ^ 2) * S ^ 2 * G + (PowerSeries.X) * S ^ 3 + (-2 * PowerSeries.X ^ 2) * c + (-4 * PowerSeries.X ^ 3) * c * G + (4 * PowerSeries.X ^ 2) * c * S + (4 * PowerSeries.X ^ 3) * c * S * G + (-2 * PowerSeries.X ^ 2) * c * S ^ 2 + (-4 * PowerSeries.X ^ 3) * c ^ 2 + (-8 * PowerSeries.X ^ 4) * c ^ 2 * G + (4 * PowerSeries.X ^ 3) * c ^ 2 * S + (-8 * PowerSeries.X ^ 4) * c ^ 3) * hc - ((-7 * PowerSeries.X + 4 * PowerSeries.X ^ 2) + (-6 * PowerSeries.X ^ 2) * G + (4 * PowerSeries.X) * S + (2 * PowerSeries.X ^ 2) * S * G + (-PowerSeries.X) * S ^ 2) * hS)
      push_cast
      linear_combination r
    | succ m =>
      have r := A026672Aux.rel (S) G (by linear_combination hS)
          (by linear_combination (16 * PowerSeries.X ^ 4) * hG - ((-PowerSeries.X) + (-2 * PowerSeries.X ^ 2) * G + (3 * PowerSeries.X) * S + (4 * PowerSeries.X ^ 2) * S * G + (-3 * PowerSeries.X) * S ^ 2 + (-2 * PowerSeries.X ^ 2) * S ^ 2 * G + (PowerSeries.X) * S ^ 3 + (-2 * PowerSeries.X ^ 2) * c + (-4 * PowerSeries.X ^ 3) * c * G + (4 * PowerSeries.X ^ 2) * c * S + (4 * PowerSeries.X ^ 3) * c * S * G + (-2 * PowerSeries.X ^ 2) * c * S ^ 2 + (-4 * PowerSeries.X ^ 3) * c ^ 2 + (-8 * PowerSeries.X ^ 4) * c ^ 2 * G + (4 * PowerSeries.X ^ 3) * c ^ 2 * S + (-8 * PowerSeries.X ^ 4) * c ^ 3) * hc - ((-7 * PowerSeries.X + 4 * PowerSeries.X ^ 2) + (-6 * PowerSeries.X ^ 2) * G + (4 * PowerSeries.X) * S + (2 * PowerSeries.X ^ 2) * S * G + (-PowerSeries.X) * S ^ 2) * hS) m
      push_cast
      linear_combination r
