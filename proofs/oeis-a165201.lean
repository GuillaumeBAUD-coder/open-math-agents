import OMAStatements.S_oeis_a165201

-- Problem: A165201: Expansion of 1/(1-x*c(x)^3), c(x) the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a165201.lean:0 (declaration OMA.S_oeis_a165201.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A165201Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-4 * X + 12 * X ^ 2 + 8 * X ^ 3 + (4 * X - 4 * X ^ 2) * S) = 8 * X ^ 3 + (0) * S) :
    (4096 - 36864 * X + 94208 * X ^ 2 - 45056 * X ^ 3 - 16384 * X ^ 4) * derivative ℚ G + (-4096 + 61440 * X ^ 2 - 8192 * X ^ 3) * G = -8192 * X + 40960 * X ^ 2 - 8192 * X ^ 3 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d96 : derivative ℚ (96 : ℚ⟦X⟧) = 0 := dnum 96
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-64 * X ^ 4 + 256 * X ^ 5 + 64 * X ^ 6) * G = (-32 * X ^ 4 + 96 * X ^ 5 + 64 * X ^ 6 : ℚ⟦X⟧) + (-32 * X ^ 4 + 32 * X ^ 5) * S := by
    linear_combination (-4 * X + 12 * X ^ 2 + 8 * X ^ 3 - (4 * X - 4 * X ^ 2) * S) * hG + (4 * X - 4 * X ^ 2) * ((4 * X - 4 * X ^ 2) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-64 * (X * X * X * X) + 256 * (X * X * X * X * X) + 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-256 * X ^ 3 + 1280 * X ^ 4 + 384 * X ^ 5) * G + (-64 * X ^ 4 + 256 * X ^ 5 + 64 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d64, d256]
    ring
  have hR : derivative ℚ ((-32 * (X * X * X * X) + 96 * (X * X * X * X * X) + 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-32 * (X * X * X * X) + 32 * (X * X * X * X * X) : ℚ⟦X⟧) * S) =
      -128 * X ^ 3 + 480 * X ^ 4 + 384 * X ^ 5 + (-128 * X ^ 3 + 160 * X ^ 4) * S + (-32 * X ^ 4 + 32 * X ^ 5) * derivative ℚ S := by
    simp [Derivation.leibniz, d32, d64, d96]
    ring
  have hk2 : (-64 * (X * X * X * X) + 256 * (X * X * X * X * X) + 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (-32 * (X * X * X * X) + 96 * (X * X * X * X * X) + 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-32 * (X * X * X * X) + 32 * (X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-256 * X ^ 3 + 1280 * X ^ 4 + 384 * X ^ 5) * G + (-64 * X ^ 4 + 256 * X ^ 5 + 64 * X ^ 6) * derivative ℚ G =
      -128 * X ^ 3 + 480 * X ^ 4 + 384 * X ^ 5 + (-128 * X ^ 3 + 160 * X ^ 4) * S + (-32 * X ^ 4 + 32 * X ^ 5) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 8 * ((4096 - 36864 * X + 94208 * X ^ 2 - 45056 * X ^ 3 - 16384 * X ^ 4) * derivative ℚ G + (-4096 + 61440 * X ^ 2 - 8192 * X ^ 3) * G - (-8192 * X + 40960 * X ^ 2 - 8192 * X ^ 3)) = 0 := by
    linear_combination (-32 * X ^ 4 + 32 * X ^ 5) ^ 2 * S * hdS - 2 * (-32 * X ^ 4 + 32 * X ^ 5) ^ 2 * derivative ℚ S * hS -
      (2 * (-128 * X ^ 3 + 160 * X ^ 4) * (1 - 4 * X) + (-32 * X ^ 4 + 32 * X ^ 5) * (-4)) * hk + 2 * (-32 * X ^ 4 + 32 * X ^ 5) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 8 ≠ 0 := pow_ne_zero 8 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-4 * X + 12 * X ^ 2 + 8 * X ^ 3 + (4 * X - 4 * X ^ 2) * S) = 8 * X ^ 3 + (0) * S) :
    (X ^ 2 - 8 * X ^ 3 + 15 * X ^ 4 + 4 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-2 * X + 6 * X ^ 2 + 6 * X ^ 3 + 10 * X ^ 4) * derivative ℚ G + (2 * X + 2 * X ^ 2 + 2 * X ^ 3) * G =
      2 * X ^ 2 + 2 * X ^ 3 := by
  have h := key S G hS hG
  have d4096 : derivative ℚ (4096 : ℚ⟦X⟧) = 0 := dnum 4096
  have d8192 : derivative ℚ (8192 : ℚ⟦X⟧) = 0 := dnum 8192
  have d16384 : derivative ℚ (16384 : ℚ⟦X⟧) = 0 := dnum 16384
  have d36864 : derivative ℚ (36864 : ℚ⟦X⟧) = 0 := dnum 36864
  have d40960 : derivative ℚ (40960 : ℚ⟦X⟧) = 0 := dnum 40960
  have d45056 : derivative ℚ (45056 : ℚ⟦X⟧) = 0 := dnum 45056
  have d61440 : derivative ℚ (61440 : ℚ⟦X⟧) = 0 := dnum 61440
  have d94208 : derivative ℚ (94208 : ℚ⟦X⟧) = 0 := dnum 94208
  have hL : derivative ℚ ((4096 - 36864 * X + 94208 * (X * X) - 45056 * (X * X * X) - 16384 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-4096 + 61440 * (X * X) - 8192 * (X * X * X) : ℚ⟦X⟧) * G) =
      (-36864 + 188416 * X - 135168 * X ^ 2 - 65536 * X ^ 3) * derivative ℚ G + (4096 - 36864 * X + 94208 * X ^ 2 - 45056 * X ^ 3 - 16384 * X ^ 4) * derivative ℚ (derivative ℚ G) + (122880 * X - 24576 * X ^ 2) * G + (-4096 + 61440 * X ^ 2 - 8192 * X ^ 3) * derivative ℚ G := by
    simp [Derivation.leibniz, d4096, d8192, d16384, d36864, d45056, d61440, d94208]
    ring
  have hRd : derivative ℚ (-8192 * X + 40960 * (X * X) - 8192 * (X * X * X) : ℚ⟦X⟧) = -8192 + 81920 * X - 24576 * X ^ 2 := by
    simp [Derivation.leibniz, d8192, d40960]
    ring
  have h2 : (4096 - 36864 * X + 94208 * (X * X) - 45056 * (X * X * X) - 16384 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-4096 + 61440 * (X * X) - 8192 * (X * X * X) : ℚ⟦X⟧) * G = (-8192 * X + 40960 * (X * X) - 8192 * (X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (-36864 + 188416 * X - 135168 * X ^ 2 - 65536 * X ^ 3) * derivative ℚ G + (4096 - 36864 * X + 94208 * X ^ 2 - 45056 * X ^ 3 - 16384 * X ^ 4) * derivative ℚ (derivative ℚ G) + (122880 * X - 24576 * X ^ 2) * G + (-4096 + 61440 * X ^ 2 - 8192 * X ^ 3) * derivative ℚ G = -8192 + 81920 * X - 24576 * X ^ 2 := by
    rw [← hL, h2, hRd]
  have hfull : (4096 - 4096 * X) * ((X ^ 2 - 8 * X ^ 3 + 15 * X ^ 4 + 4 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-2 * X + 6 * X ^ 2 + 6 * X ^ 3 + 10 * X ^ 4) * derivative ℚ G + (2 * X + 2 * X ^ 2 + 2 * X ^ 3) * G - (2 * X ^ 2 + 2 * X ^ 3)) = 0 := by
    linear_combination (X ^ 2) * hd + (-2 * X) * h
  have hg : (4096 - 4096 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (4096 : ℚ⟦X⟧) = 4096 := cnum 4096
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-4 * X + 12 * X ^ 2 + 8 * X ^ 3 + (4 * X - 4 * X ^ 2) * S) = 8 * X ^ 3 + (0) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C 1 + derivative ℚ (derivative ℚ G) * X * X * X * C (-8) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 15 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 4 +
      derivative ℚ G * X * C (-2) + derivative ℚ G * X * X * C 6 +
      derivative ℚ G * X * X * X * C 6 + derivative ℚ G * X * X * X * X * C 10 +
      G * X * C 2 + G * X * X * C 2 +
      G * X * X * X * C 2 =
      C 2 * X * X + C 2 * X * X * X := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-4 * X + 12 * X ^ 2 + 8 * X ^ 3 + (4 * X - 4 * X ^ 2) * S) = 8 * X ^ 3 + (0) * S) (m : ℕ) :
    1 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-8) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      15 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + 4 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      (-2) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 6 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      6 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 10 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      2 * coeff (m + 1 + 1 + 1 + 1) G + 2 * coeff (m + 1 + 1 + 1) G +
      2 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-4 * X + 12 * X ^ 2 + 8 * X ^ 3 + (4 * X - 4 * X ^ 2) * S) = 8 * X ^ 3 + (0) * S) :
    12 * coeff (0 + 1 + 1 + 1 + 1) G + (-48) * coeff (0 + 1 + 1 + 1) G +
      30 * coeff (0 + 1 + 1) G + (-8) * coeff (0 + 1 + 1 + 1 + 1) G +
      18 * coeff (0 + 1 + 1 + 1) G + 12 * coeff (0 + 1 + 1) G +
      10 * coeff (0 + 1) G + 2 * coeff (0 + 1 + 1 + 1) G +
      2 * coeff (0 + 1 + 1) G + 2 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A165201Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a165201.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  rw [e1, e2, e3]
  cases m with
  | zero =>
    have r := A165201Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (8 * PowerSeries.X ^ 3) * hG - ((-PowerSeries.X) * G + (2 * PowerSeries.X) * S * G + (-PowerSeries.X) * S ^ 2 * G + (-2 * PowerSeries.X ^ 2) * c * G + (2 * PowerSeries.X ^ 2) * c * S * G + (-4 * PowerSeries.X ^ 3) * c ^ 2 * G) * hc - ((-3 * PowerSeries.X) * G + (PowerSeries.X) * S * G) * hS)
    push_cast
    linear_combination r
  | succ m =>
    have r := A165201Aux.rel (S) G (by linear_combination hS)
        (by linear_combination (8 * PowerSeries.X ^ 3) * hG - ((-PowerSeries.X) * G + (2 * PowerSeries.X) * S * G + (-PowerSeries.X) * S ^ 2 * G + (-2 * PowerSeries.X ^ 2) * c * G + (2 * PowerSeries.X ^ 2) * c * S * G + (-4 * PowerSeries.X ^ 3) * c ^ 2 * G) * hc - ((-3 * PowerSeries.X) * G + (PowerSeries.X) * S * G) * hS) m
    push_cast
    linear_combination r
