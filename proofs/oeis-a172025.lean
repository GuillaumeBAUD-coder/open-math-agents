import OMAStatements.S_oeis_a172025

-- Problem: A172025: Expansion of (2/(3*sqrt(1-4*z)-1+4*z))*((1-sqrt(1-4*z))/(2*z))^k with k=3.
-- Upstream: formal-conjectures statements/oeis-a172025.lean:0 (declaration OMA.S_oeis_a172025.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A172025Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-8 * X ^ 3 + 32 * X ^ 4 + (24 * X ^ 3) * S) = 8 - 24 * X + (-8 + 8 * X) * S) :
    (131072 * X - 720896 * X ^ 2 + 393216 * X ^ 3 + 1441792 * X ^ 4 + 524288 * X ^ 5) * derivative ℚ G + (393216 - 2097152 * X + 786432 * X ^ 2 + 3145728 * X ^ 3 + 1310720 * X ^ 4) * G = 393216 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have d512 : derivative ℚ (512 : ℚ⟦X⟧) = 0 := dnum 512
  have d1024 : derivative ℚ (1024 : ℚ⟦X⟧) = 0 := dnum 1024
  have d1792 : derivative ℚ (1792 : ℚ⟦X⟧) = 0 := dnum 1792
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-512 * X ^ 6 + 1792 * X ^ 7 + 1024 * X ^ 8) * G = (128 * X ^ 3 - 512 * X ^ 4 : ℚ⟦X⟧) + (-128 * X ^ 3 + 256 * X ^ 4 + 256 * X ^ 5) * S := by
    linear_combination (-8 * X ^ 3 + 32 * X ^ 4 - (24 * X ^ 3) * S) * hG + (24 * X ^ 3) * ((24 * X ^ 3) * G - (-8 + 8 * X)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-512 * (X * X * X * X * X * X) + 1792 * (X * X * X * X * X * X * X) + 1024 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-3072 * X ^ 5 + 12544 * X ^ 6 + 8192 * X ^ 7) * G + (-512 * X ^ 6 + 1792 * X ^ 7 + 1024 * X ^ 8) * derivative ℚ G := by
    simp [Derivation.leibniz, d512, d1024, d1792]
    ring
  have hR : derivative ℚ ((128 * (X * X * X) - 512 * (X * X * X * X) : ℚ⟦X⟧) + (-128 * (X * X * X) + 256 * (X * X * X * X) + 256 * (X * X * X * X * X) : ℚ⟦X⟧) * S) =
      384 * X ^ 2 - 2048 * X ^ 3 + (-384 * X ^ 2 + 1024 * X ^ 3 + 1280 * X ^ 4) * S + (-128 * X ^ 3 + 256 * X ^ 4 + 256 * X ^ 5) * derivative ℚ S := by
    simp [Derivation.leibniz, d128, d256, d512]
    ring
  have hk2 : (-512 * (X * X * X * X * X * X) + 1792 * (X * X * X * X * X * X * X) + 1024 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (128 * (X * X * X) - 512 * (X * X * X * X) : ℚ⟦X⟧) + (-128 * (X * X * X) + 256 * (X * X * X * X) + 256 * (X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-3072 * X ^ 5 + 12544 * X ^ 6 + 8192 * X ^ 7) * G + (-512 * X ^ 6 + 1792 * X ^ 7 + 1024 * X ^ 8) * derivative ℚ G =
      384 * X ^ 2 - 2048 * X ^ 3 + (-384 * X ^ 2 + 1024 * X ^ 3 + 1280 * X ^ 4) * S + (-128 * X ^ 3 + 256 * X ^ 4 + 256 * X ^ 5) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 8 * ((1 - 4 * X) * ((131072 * X - 720896 * X ^ 2 + 393216 * X ^ 3 + 1441792 * X ^ 4 + 524288 * X ^ 5) * derivative ℚ G + (393216 - 2097152 * X + 786432 * X ^ 2 + 3145728 * X ^ 3 + 1310720 * X ^ 4) * G - (393216))) = 0 := by
    linear_combination (-128 * X ^ 3 + 256 * X ^ 4 + 256 * X ^ 5) ^ 2 * S * hdS - 2 * (-128 * X ^ 3 + 256 * X ^ 4 + 256 * X ^ 5) ^ 2 * derivative ℚ S * hS -
      (2 * (-384 * X ^ 2 + 1024 * X ^ 3 + 1280 * X ^ 4) * (1 - 4 * X) + (-128 * X ^ 3 + 256 * X ^ 4 + 256 * X ^ 5) * (-4)) * hk + 2 * (-128 * X ^ 3 + 256 * X ^ 4 + 256 * X ^ 5) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 8 ≠ 0 := pow_ne_zero 8 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-8 * X ^ 3 + 32 * X ^ 4 + (24 * X ^ 3) * S) = 8 - 24 * X + (-8 + 8 * X) * S) :
    (2 * X ^ 2 - 7 * X ^ 3 - 4 * X ^ 4) * derivative ℚ (derivative ℚ G) + (8 * X - 38 * X ^ 2 - 30 * X ^ 3) * derivative ℚ G + (-32 * X - 40 * X ^ 2) * G =
      0 := by
  have h := key S G hS hG
  have d131072 : derivative ℚ (131072 : ℚ⟦X⟧) = 0 := dnum 131072
  have d393216 : derivative ℚ (393216 : ℚ⟦X⟧) = 0 := dnum 393216
  have d524288 : derivative ℚ (524288 : ℚ⟦X⟧) = 0 := dnum 524288
  have d720896 : derivative ℚ (720896 : ℚ⟦X⟧) = 0 := dnum 720896
  have d786432 : derivative ℚ (786432 : ℚ⟦X⟧) = 0 := dnum 786432
  have d1310720 : derivative ℚ (1310720 : ℚ⟦X⟧) = 0 := dnum 1310720
  have d1441792 : derivative ℚ (1441792 : ℚ⟦X⟧) = 0 := dnum 1441792
  have d2097152 : derivative ℚ (2097152 : ℚ⟦X⟧) = 0 := dnum 2097152
  have d3145728 : derivative ℚ (3145728 : ℚ⟦X⟧) = 0 := dnum 3145728
  have hL : derivative ℚ ((131072 * X - 720896 * (X * X) + 393216 * (X * X * X) + 1441792 * (X * X * X * X) + 524288 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (393216 - 2097152 * X + 786432 * (X * X) + 3145728 * (X * X * X) + 1310720 * (X * X * X * X) : ℚ⟦X⟧) * G) =
      (131072 - 1441792 * X + 1179648 * X ^ 2 + 5767168 * X ^ 3 + 2621440 * X ^ 4) * derivative ℚ G + (131072 * X - 720896 * X ^ 2 + 393216 * X ^ 3 + 1441792 * X ^ 4 + 524288 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-2097152 + 1572864 * X + 9437184 * X ^ 2 + 5242880 * X ^ 3) * G + (393216 - 2097152 * X + 786432 * X ^ 2 + 3145728 * X ^ 3 + 1310720 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d131072, d393216, d524288, d720896, d786432, d1310720, d1441792, d2097152, d3145728]
    ring
  have hRd : derivative ℚ (393216 : ℚ⟦X⟧) = 0 := by
    simp [d393216]
  have h2 : (131072 * X - 720896 * (X * X) + 393216 * (X * X * X) + 1441792 * (X * X * X * X) + 524288 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (393216 - 2097152 * X + 786432 * (X * X) + 3145728 * (X * X * X) + 1310720 * (X * X * X * X) : ℚ⟦X⟧) * G = (393216 : ℚ⟦X⟧) := by linear_combination h
  have hd : (131072 - 1441792 * X + 1179648 * X ^ 2 + 5767168 * X ^ 3 + 2621440 * X ^ 4) * derivative ℚ G + (131072 * X - 720896 * X ^ 2 + 393216 * X ^ 3 + 1441792 * X ^ 4 + 524288 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-2097152 + 1572864 * X + 9437184 * X ^ 2 + 5242880 * X ^ 3) * G + (393216 - 2097152 * X + 786432 * X ^ 2 + 3145728 * X ^ 3 + 1310720 * X ^ 4) * derivative ℚ G = 0 := by
    rw [← hL, h2, hRd]
  have hfull : (65536 - 131072 * X - 131072 * X ^ 2) * ((2 * X ^ 2 - 7 * X ^ 3 - 4 * X ^ 4) * derivative ℚ (derivative ℚ G) + (8 * X - 38 * X ^ 2 - 30 * X ^ 3) * derivative ℚ G + (-32 * X - 40 * X ^ 2) * G - (0)) = 0 := by
    linear_combination (X) * hd + (0) * h
  have hg : (65536 - 131072 * X - 131072 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (65536 : ℚ⟦X⟧) = 65536 := cnum 65536
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-8 * X ^ 3 + 32 * X ^ 4 + (24 * X ^ 3) * S) = 8 - 24 * X + (-8 + 8 * X) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C 2 + derivative ℚ (derivative ℚ G) * X * X * X * C (-7) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-4) + derivative ℚ G * X * C 8 +
      derivative ℚ G * X * X * C (-38) + derivative ℚ G * X * X * X * C (-30) +
      G * X * C (-32) + G * X * X * C (-40) =
      0 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-8 * X ^ 3 + 32 * X ^ 4 + (24 * X ^ 3) * S) = 8 - 24 * X + (-8 + 8 * X) * S) (m : ℕ) :
    2 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-7) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-4) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + 8 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-38) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-30) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-32) * coeff (m + 1 + 1 + 1) G + (-40) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-8 * X ^ 3 + 32 * X ^ 4 + (24 * X ^ 3) * S) = 8 - 24 * X + (-8 + 8 * X) * S) :
    4 * coeff (0 + 1 + 1) G + 16 * coeff (0 + 1 + 1) G +
      (-38) * coeff (0 + 1) G + (-32) * coeff (0 + 1) G +
      (-40) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-8 * X ^ 3 + 32 * X ^ 4 + (24 * X ^ 3) * S) = 8 - 24 * X + (-8 + 8 * X) * S) :
    12 * coeff (0 + 1 + 1 + 1) G + (-14) * coeff (0 + 1 + 1) G +
      24 * coeff (0 + 1 + 1 + 1) G + (-76) * coeff (0 + 1 + 1) G +
      (-30) * coeff (0 + 1) G + (-32) * coeff (0 + 1 + 1) G +
      (-40) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A172025Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a172025.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A172025Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (8 * PowerSeries.X ^ 3) * hG - ((-2) + (4) * S + (-2) * S ^ 2 + (-4 * PowerSeries.X) * c + (4 * PowerSeries.X) * c * S + (-8 * PowerSeries.X ^ 2) * c ^ 2) * hc - ((-6) + (2) * S) * hS)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A172025Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination (8 * PowerSeries.X ^ 3) * hG - ((-2) + (4) * S + (-2) * S ^ 2 + (-4 * PowerSeries.X) * c + (4 * PowerSeries.X) * c * S + (-8 * PowerSeries.X ^ 2) * c ^ 2) * hc - ((-6) + (2) * S) * hS)
      push_cast
      linear_combination r
    | succ m =>
      have r := A172025Aux.rel (S) G (by linear_combination hS)
          (by linear_combination (8 * PowerSeries.X ^ 3) * hG - ((-2) + (4) * S + (-2) * S ^ 2 + (-4 * PowerSeries.X) * c + (4 * PowerSeries.X) * c * S + (-8 * PowerSeries.X ^ 2) * c ^ 2) * hc - ((-6) + (2) * S) * hS) m
      push_cast
      linear_combination r
