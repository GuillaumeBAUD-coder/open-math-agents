import OMAStatements.S_oeis_a188314

-- Problem: A188314: Expansion of (1/(1-x))*c(x/((1-x)*(1-x^2))) where c(x) is the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a188314.lean:0 (declaration OMA.S_oeis_a188314.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A188314Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 6 * X ^ 2 + X ^ 4)
    (hG : G * (2 * X + (0) * S) = 1 - X ^ 2 + (-1) * S) :
    (-4 * X + 16 * X ^ 2 + 24 * X ^ 3 - 4 * X ^ 5) * derivative ℚ G + (-4 + 8 * X + 4 * X ^ 4) * G = -4 - 8 * X - 12 * X ^ 2 - 8 * X ^ 3 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have hS2 : S * S = (1 - 4 * X - 6 * (X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (2 * X) * G = (1 - X ^ 2 : ℚ⟦X⟧) + (-1) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * X - 6 * (X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) = -4 - 12 * X + 4 * X ^ 3 := by
    simp [Derivation.leibniz, d4, d6]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 - 12 * X + 4 * X ^ 3 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((2 * X : ℚ⟦X⟧) * G) = (2) * G + (2 * X) * derivative ℚ G := by
    simp [Derivation.leibniz, d2]
    ring
  have hR : derivative ℚ ((1 - 1 * (X * X) : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S) =
      -2 * X + (0) * S + (-1) * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hk2 : (2 * X : ℚ⟦X⟧) * G = (1 - 1 * (X * X) : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (2) * G + (2 * X) * derivative ℚ G =
      -2 * X + (0) * S + (-1) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (-1) ^ 2 * S * hdS - 2 * (-1) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 - 4 * X - 6 * X ^ 2 + X ^ 4) + (-1) * (-4 - 12 * X + 4 * X ^ 3)) * hk + 2 * (-1) * (1 - 4 * X - 6 * X ^ 2 + X ^ 4) * hdk

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 6 * X ^ 2 + X ^ 4)
    (hG : G * (2 * X + (0) * S) = 1 - X ^ 2 + (-1) * S) :
    derivative ℚ G * X * C (-4) + derivative ℚ G * X * X * C 16 +
      derivative ℚ G * X * X * X * C 24 + derivative ℚ G * X * X * X * X * X * C (-4) +
      G * C (-4) + G * X * C 8 +
      G * X * X * X * X * C 4 =
      C (-4) + C (-8) * X +
      C (-12) * X * X + C (-8) * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 6 * X ^ 2 + X ^ 4)
    (hG : G * (2 * X + (0) * S) = 1 - X ^ 2 + (-1) * S) (m : ℕ) :
    (-4) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 16 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      24 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-4) * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 8 * coeff (m + 1 + 1 + 1 + 1) G +
      4 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 6 * X ^ 2 + X ^ 4)
    (hG : G * (2 * X + (0) * S) = 1 - X ^ 2 + (-1) * S) :
    (-16) * coeff (0 + 1 + 1 + 1 + 1) G + 48 * coeff (0 + 1 + 1 + 1) G +
      48 * coeff (0 + 1 + 1) G + (-4) * coeff (0 + 1 + 1 + 1 + 1) G +
      8 * coeff (0 + 1 + 1 + 1) G + 4 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A188314Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a188314.main := by
  intro T G hT _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 - 5 = m := rfl
  rw [e1, e2, e3, e4, e5]
  cases m with
  | zero =>
    have r0 := A188314Aux.rel ((1 - PowerSeries.X ^ 2) * T) G (by linear_combination (1 + PowerSeries.X) * hT)
        (by linear_combination hG) 0
    have r1 := A188314Aux.relE0 ((1 - PowerSeries.X ^ 2) * T) G (by linear_combination (1 + PowerSeries.X) * hT)
        (by linear_combination hG)
    push_cast at r0 r1 ⊢
    linear_combination ((-1 : ℚ) / 4) * r0 + ((-5 : ℚ) / 4) * r1
  | succ m =>
    have r0 := A188314Aux.rel ((1 - PowerSeries.X ^ 2) * T) G (by linear_combination (1 + PowerSeries.X) * hT)
        (by linear_combination hG) (m + 1)
    have r1 := A188314Aux.rel ((1 - PowerSeries.X ^ 2) * T) G (by linear_combination (1 + PowerSeries.X) * hT)
        (by linear_combination hG) m
    push_cast at r0 r1 ⊢
    linear_combination ((1 : ℚ) / 4) * ((-1) * r0 + (-5) * r1)
