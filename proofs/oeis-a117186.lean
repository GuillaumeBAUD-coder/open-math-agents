import OMAStatements.S_oeis_a117186

-- Problem: A117186: Expansion of (1+x)c(x^2)/((1-xc(x^2))*sqrt(1-4x^2)), c(x) the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a117186.lean:0 (declaration OMA.S_oeis_a117186.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A117186Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (X - 4 * X ^ 3 + (-X + 2 * X ^ 2) * S) = 1 + X + (-1 - X) * S) :
    (-16 * X + 16 * X ^ 2 + 96 * X ^ 3 - 64 * X ^ 4 - 128 * X ^ 5) * derivative ℚ G + (-16 + 32 * X + 128 * X ^ 2 - 192 * X ^ 3 - 128 * X ^ 4) * G = -16 - 32 * X - 16 * X ^ 2 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have hS2 : S * S = (1 - 4 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (4 * X ^ 3 - 8 * X ^ 4 - 16 * X ^ 5 + 32 * X ^ 6) * G = (2 * X ^ 2 + 2 * X ^ 3 - 8 * X ^ 4 - 8 * X ^ 5 : ℚ⟦X⟧) + (-2 * X ^ 2 + 2 * X ^ 3 + 4 * X ^ 4) * S := by
    linear_combination (X - 4 * X ^ 3 - (-X + 2 * X ^ 2) * S) * hG + (-X + 2 * X ^ 2) * ((-X + 2 * X ^ 2) * G - (-1 - X)) * hS
  have hPd : derivative ℚ (1 - 4 * (X * X) : ℚ⟦X⟧) = -8 * X := by
    simp [Derivation.leibniz, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((4 * (X * X * X) - 8 * (X * X * X * X) - 16 * (X * X * X * X * X) + 32 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (12 * X ^ 2 - 32 * X ^ 3 - 80 * X ^ 4 + 192 * X ^ 5) * G + (4 * X ^ 3 - 8 * X ^ 4 - 16 * X ^ 5 + 32 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d8, d16, d32]
    ring
  have hR : derivative ℚ ((2 * (X * X) + 2 * (X * X * X) - 8 * (X * X * X * X) - 8 * (X * X * X * X * X) : ℚ⟦X⟧) + (-2 * (X * X) + 2 * (X * X * X) + 4 * (X * X * X * X) : ℚ⟦X⟧) * S) =
      4 * X + 6 * X ^ 2 - 32 * X ^ 3 - 40 * X ^ 4 + (-4 * X + 6 * X ^ 2 + 16 * X ^ 3) * S + (-2 * X ^ 2 + 2 * X ^ 3 + 4 * X ^ 4) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d4, d8]
    ring
  have hk2 : (4 * (X * X * X) - 8 * (X * X * X * X) - 16 * (X * X * X * X * X) + 32 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (2 * (X * X) + 2 * (X * X * X) - 8 * (X * X * X * X) - 8 * (X * X * X * X * X) : ℚ⟦X⟧) + (-2 * (X * X) + 2 * (X * X * X) + 4 * (X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (12 * X ^ 2 - 32 * X ^ 3 - 80 * X ^ 4 + 192 * X ^ 5) * G + (4 * X ^ 3 - 8 * X ^ 4 - 16 * X ^ 5 + 32 * X ^ 6) * derivative ℚ G =
      4 * X + 6 * X ^ 2 - 32 * X ^ 3 - 40 * X ^ 4 + (-4 * X + 6 * X ^ 2 + 16 * X ^ 3) * S + (-2 * X ^ 2 + 2 * X ^ 3 + 4 * X ^ 4) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 4 * ((1 - 2 * X - 4 * X ^ 2 + 8 * X ^ 3) * ((-16 * X + 16 * X ^ 2 + 96 * X ^ 3 - 64 * X ^ 4 - 128 * X ^ 5) * derivative ℚ G + (-16 + 32 * X + 128 * X ^ 2 - 192 * X ^ 3 - 128 * X ^ 4) * G - (-16 - 32 * X - 16 * X ^ 2))) = 0 := by
    linear_combination (-2 * X ^ 2 + 2 * X ^ 3 + 4 * X ^ 4) ^ 2 * S * hdS - 2 * (-2 * X ^ 2 + 2 * X ^ 3 + 4 * X ^ 4) ^ 2 * derivative ℚ S * hS -
      (2 * (-4 * X + 6 * X ^ 2 + 16 * X ^ 3) * (1 - 4 * X ^ 2) + (-2 * X ^ 2 + 2 * X ^ 3 + 4 * X ^ 4) * (-8 * X)) * hk + 2 * (-2 * X ^ 2 + 2 * X ^ 3 + 4 * X ^ 4) * (1 - 4 * X ^ 2) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 4 ≠ 0 := pow_ne_zero 4 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 2 * X - 4 * X ^ 2 + 8 * X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (X - 4 * X ^ 3 + (-X + 2 * X ^ 2) * S) = 1 + X + (-1 - X) * S) :
    derivative ℚ G * X * C (-16) + derivative ℚ G * X * X * C 16 +
      derivative ℚ G * X * X * X * C 96 + derivative ℚ G * X * X * X * X * C (-64) +
      derivative ℚ G * X * X * X * X * X * C (-128) + G * C (-16) +
      G * X * C 32 + G * X * X * C 128 +
      G * X * X * X * C (-192) + G * X * X * X * X * C (-128) =
      C (-16) + C (-32) * X +
      C (-16) * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (X - 4 * X ^ 3 + (-X + 2 * X ^ 2) * S) = 1 + X + (-1 - X) * S) (m : ℕ) :
    (-16) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 16 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      96 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-64) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-128) * ((m : ℚ) + 1) * coeff (m + 1) G + (-16) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      32 * coeff (m + 1 + 1 + 1 + 1) G + 128 * coeff (m + 1 + 1 + 1) G +
      (-192) * coeff (m + 1 + 1) G + (-128) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (X - 4 * X ^ 3 + (-X + 2 * X ^ 2) * S) = 1 + X + (-1 - X) * S) :
    (-64) * coeff (0 + 1 + 1 + 1 + 1) G + 48 * coeff (0 + 1 + 1 + 1) G +
      192 * coeff (0 + 1 + 1) G + (-64) * coeff (0 + 1) G +
      (-16) * coeff (0 + 1 + 1 + 1 + 1) G + 32 * coeff (0 + 1 + 1 + 1) G +
      128 * coeff (0 + 1 + 1) G + (-192) * coeff (0 + 1) G +
      (-128) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A117186Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a117186.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  cases m with
  | zero =>
    have r := A117186Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (2 * PowerSeries.X ^ 2) * hG - ((-1 - PowerSeries.X) + (-PowerSeries.X) * S * G) * hc - ((PowerSeries.X) * G) * hS)
    push_cast
    linear_combination ((1 : ℚ) / 16) * r
  | succ m =>
    have r := A117186Aux.rel (S) G (by linear_combination hS)
        (by linear_combination (2 * PowerSeries.X ^ 2) * hG - ((-1 - PowerSeries.X) + (-PowerSeries.X) * S * G) * hc - ((PowerSeries.X) * G) * hS) m
    push_cast
    linear_combination ((1 : ℚ) / 16) * r
