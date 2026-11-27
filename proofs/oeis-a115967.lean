import OMAStatements.S_oeis_a115967

-- Problem: A115967: Expansion of 1/(2*sqrt(1-2*x-3*x^2) - 1).
-- Upstream: formal-conjectures statements/oeis-a115967.lean:0 (declaration OMA.S_oeis_a115967.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A115967Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (-1 + (2) * S) = 1 + (0) * S) :
    (12 - 56 * X - 20 * X ^ 2 + 192 * X ^ 3 + 144 * X ^ 4) * derivative ℚ G + (-20 - 28 * X + 144 * X ^ 2 + 144 * X ^ 3) * G = 4 + 12 * X := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have hS2 : S * S = (1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-3 + 8 * X + 12 * X ^ 2) * G = (-1 : ℚ⟦X⟧) + (-2) * S := by
    linear_combination (-1 - (2) * S) * hG + (2) * ((2) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) = -2 - 6 * X := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -2 - 6 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-3 + 8 * X + 12 * (X * X) : ℚ⟦X⟧) * G) = (8 + 24 * X) * G + (-3 + 8 * X + 12 * X ^ 2) * derivative ℚ G := by
    simp [Derivation.leibniz, d3, d8, d12]
    ring
  have hR : derivative ℚ ((-1 : ℚ⟦X⟧) + (-2 : ℚ⟦X⟧) * S) =
      0 + (0) * S + (-2) * derivative ℚ S := by
    simp [Derivation.leibniz, d2]
  have hk2 : (-3 + 8 * X + 12 * (X * X) : ℚ⟦X⟧) * G = (-1 : ℚ⟦X⟧) + (-2 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (8 + 24 * X) * G + (-3 + 8 * X + 12 * X ^ 2) * derivative ℚ G =
      0 + (0) * S + (-2) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (-2) ^ 2 * S * hdS - 2 * (-2) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 - 2 * X - 3 * X ^ 2) + (-2) * (-2 - 6 * X)) * hk + 2 * (-2) * (1 - 2 * X - 3 * X ^ 2) * hdk

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (-1 + (2) * S) = 1 + (0) * S) :
    derivative ℚ G * C 12 + derivative ℚ G * X * C (-56) +
      derivative ℚ G * X * X * C (-20) + derivative ℚ G * X * X * X * C 192 +
      derivative ℚ G * X * X * X * X * C 144 + G * C (-20) +
      G * X * C (-28) + G * X * X * C 144 +
      G * X * X * X * C 144 =
      C 4 + C 12 * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (-1 + (2) * S) = 1 + (0) * S) (m : ℕ) :
    12 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-56) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-20) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 192 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      144 * ((m : ℚ) + 1) * coeff (m + 1) G + (-20) * coeff (m + 1 + 1 + 1 + 1) G +
      (-28) * coeff (m + 1 + 1 + 1) G + 144 * coeff (m + 1 + 1) G +
      144 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (-1 + (2) * S) = 1 + (0) * S) :
    48 * coeff (0 + 1 + 1 + 1 + 1) G + (-168) * coeff (0 + 1 + 1 + 1) G +
      (-40) * coeff (0 + 1 + 1) G + 192 * coeff (0 + 1) G +
      (-20) * coeff (0 + 1 + 1 + 1) G + (-28) * coeff (0 + 1 + 1) G +
      144 * coeff (0 + 1) G + 144 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A115967Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a115967.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  cases m with
  | zero =>
    have r := A115967Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination ((1 : ℚ) / 4) * r
  | succ m =>
    have r := A115967Aux.rel (S) G (by linear_combination hS)
        (by linear_combination hG) m
    push_cast
    linear_combination ((1 : ℚ) / 4) * r
