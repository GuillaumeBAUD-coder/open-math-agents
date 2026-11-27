import OMAStatements.S_oeis_a071717

-- Problem: A071717: Expansion of (1 + x^2*C)*C^2, where C = (1 - sqrt(1-4*x))/(2*x) is g.f. for Catalan numbers, A000108.
-- Upstream: formal-conjectures statements/oeis-a071717.lean:0 (declaration OMA.S_oeis_a071717.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A071717Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (8 * X ^ 3 + (0) * S) = 4 * X - 4 * X ^ 2 - 12 * X ^ 3 + (-4 * X - 4 * X ^ 2 + 4 * X ^ 3) * S) :
    (-64 * X + 192 * X ^ 2 + 320 * X ^ 3 - 256 * X ^ 4) * derivative ℚ G + (-128 + 320 * X + 128 * X ^ 2 + 128 * X ^ 3) * G = -128 - 64 * X - 384 * X ^ 2 - 192 * X ^ 3 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (8 * X ^ 3) * G = (4 * X - 4 * X ^ 2 - 12 * X ^ 3 : ℚ⟦X⟧) + (-4 * X - 4 * X ^ 2 + 4 * X ^ 3) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((8 * (X * X * X) : ℚ⟦X⟧) * G) = (24 * X ^ 2) * G + (8 * X ^ 3) * derivative ℚ G := by
    simp [Derivation.leibniz, d8]
    ring
  have hR : derivative ℚ ((4 * X - 4 * (X * X) - 12 * (X * X * X) : ℚ⟦X⟧) + (-4 * X - 4 * (X * X) + 4 * (X * X * X) : ℚ⟦X⟧) * S) =
      4 - 8 * X - 36 * X ^ 2 + (-4 - 8 * X + 12 * X ^ 2) * S + (-4 * X - 4 * X ^ 2 + 4 * X ^ 3) * derivative ℚ S := by
    simp [Derivation.leibniz, d4, d12]
    ring
  have hk2 : (8 * (X * X * X) : ℚ⟦X⟧) * G = (4 * X - 4 * (X * X) - 12 * (X * X * X) : ℚ⟦X⟧) + (-4 * X - 4 * (X * X) + 4 * (X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (24 * X ^ 2) * G + (8 * X ^ 3) * derivative ℚ G =
      4 - 8 * X - 36 * X ^ 2 + (-4 - 8 * X + 12 * X ^ 2) * S + (-4 * X - 4 * X ^ 2 + 4 * X ^ 3) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 3 * ((-64 * X + 192 * X ^ 2 + 320 * X ^ 3 - 256 * X ^ 4) * derivative ℚ G + (-128 + 320 * X + 128 * X ^ 2 + 128 * X ^ 3) * G - (-128 - 64 * X - 384 * X ^ 2 - 192 * X ^ 3)) = 0 := by
    linear_combination (-4 * X - 4 * X ^ 2 + 4 * X ^ 3) ^ 2 * S * hdS - 2 * (-4 * X - 4 * X ^ 2 + 4 * X ^ 3) ^ 2 * derivative ℚ S * hS -
      (2 * (-4 - 8 * X + 12 * X ^ 2) * (1 - 4 * X) + (-4 * X - 4 * X ^ 2 + 4 * X ^ 3) * (-4)) * hk + 2 * (-4 * X - 4 * X ^ 2 + 4 * X ^ 3) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 3 ≠ 0 := pow_ne_zero 3 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (8 * X ^ 3 + (0) * S) = 4 * X - 4 * X ^ 2 - 12 * X ^ 3 + (-4 * X - 4 * X ^ 2 + 4 * X ^ 3) * S) :
    derivative ℚ G * X * C (-64) + derivative ℚ G * X * X * C 192 +
      derivative ℚ G * X * X * X * C 320 + derivative ℚ G * X * X * X * X * C (-256) +
      G * C (-128) + G * X * C 320 +
      G * X * X * C 128 + G * X * X * X * C 128 =
      C (-128) + C (-64) * X +
      C (-384) * X * X + C (-192) * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (8 * X ^ 3 + (0) * S) = 4 * X - 4 * X ^ 2 - 12 * X ^ 3 + (-4 * X - 4 * X ^ 2 + 4 * X ^ 3) * S) (m : ℕ) :
    (-64) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 192 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      320 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-256) * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-128) * coeff (m + 1 + 1 + 1 + 1) G + 320 * coeff (m + 1 + 1 + 1) G +
      128 * coeff (m + 1 + 1) G + 128 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

end A071717Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a071717.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  rw [e1, e2, e3]
  have r := A071717Aux.rel (S) G (by linear_combination hS)
      (by linear_combination (8 * PowerSeries.X ^ 3) * hG - ((-2 * PowerSeries.X - PowerSeries.X ^ 2) + (2 * PowerSeries.X + 2 * PowerSeries.X ^ 2) * S + (-PowerSeries.X ^ 2) * S ^ 2 + (-4 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3) * c + (2 * PowerSeries.X ^ 3) * c * S + (-4 * PowerSeries.X ^ 4) * c ^ 2) * hc - ((-2 * PowerSeries.X - 3 * PowerSeries.X ^ 2) + (PowerSeries.X ^ 2) * S) * hS) m
  push_cast
  linear_combination ((-1 : ℚ) / 64) * r
