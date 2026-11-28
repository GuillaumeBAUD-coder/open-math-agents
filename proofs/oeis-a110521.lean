import OMAStatements.S_oeis_a110521

-- Problem: A110521: Expansion of 1/(1 - (x + x^2)c(3x)), c(x) the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a110521.lean:0 (declaration OMA.S_oeis_a110521.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A110521Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 12 * X)
    (hG : G * (5 - X + (1 + X) * S) = 6 + (0) * S) :
    (-288 + 3168 * X + 3168 * X ^ 2 + 3024 * X ^ 3 + 5040 * X ^ 4 + 1728 * X ^ 5) * derivative ℚ G + (-1440 - 5760 * X + 4464 * X ^ 2 + 5760 * X ^ 3 + 2592 * X ^ 4) * G = -1728 - 6912 * X + 432 * X ^ 2 := by
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d30 : derivative ℚ (30 : ℚ⟦X⟧) = 0 := dnum 30
  have hS2 : S * S = (1 - 12 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (24 + 24 * X ^ 2 + 12 * X ^ 3) * G = (30 - 6 * X : ℚ⟦X⟧) + (-6 - 6 * X) * S := by
    linear_combination (5 - X - (1 + X) * S) * hG + (1 + X) * ((1 + X) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 12 * X : ℚ⟦X⟧) = -12 := by
    simp [Derivation.leibniz, d12]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -12 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((24 + 24 * (X * X) + 12 * (X * X * X) : ℚ⟦X⟧) * G) = (48 * X + 36 * X ^ 2) * G + (24 + 24 * X ^ 2 + 12 * X ^ 3) * derivative ℚ G := by
    simp [Derivation.leibniz, d12, d24]
    ring
  have hR : derivative ℚ ((30 - 6 * X : ℚ⟦X⟧) + (-6 - 6 * X : ℚ⟦X⟧) * S) =
      -6 + (-6) * S + (-6 - 6 * X) * derivative ℚ S := by
    simp [Derivation.leibniz, d6, d30]
    ring
  have hk2 : (24 + 24 * (X * X) + 12 * (X * X * X) : ℚ⟦X⟧) * G = (30 - 6 * X : ℚ⟦X⟧) + (-6 - 6 * X : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (48 * X + 36 * X ^ 2) * G + (24 + 24 * X ^ 2 + 12 * X ^ 3) * derivative ℚ G =
      -6 + (-6) * S + (-6 - 6 * X) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (-6 - 6 * X) ^ 2 * S * hdS - 2 * (-6 - 6 * X) ^ 2 * derivative ℚ S * hS -
      (2 * (-6) * (1 - 12 * X) + (-6 - 6 * X) * (-12)) * hk + 2 * (-6 - 6 * X) * (1 - 12 * X) * hdk

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 12 * X)
    (hG : G * (5 - X + (1 + X) * S) = 6 + (0) * S) :
    derivative ℚ G * C (-288) + derivative ℚ G * X * C 3168 +
      derivative ℚ G * X * X * C 3168 + derivative ℚ G * X * X * X * C 3024 +
      derivative ℚ G * X * X * X * X * C 5040 + derivative ℚ G * X * X * X * X * X * C 1728 +
      G * C (-1440) + G * X * C (-5760) +
      G * X * X * C 4464 + G * X * X * X * C 5760 +
      G * X * X * X * X * C 2592 =
      C (-1728) + C (-6912) * X +
      C 432 * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 12 * X)
    (hG : G * (5 - X + (1 + X) * S) = 6 + (0) * S) (m : ℕ) :
    (-288) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 3168 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      3168 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 3024 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      5040 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + 1728 * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-1440) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-5760) * coeff (m + 1 + 1 + 1 + 1) G +
      4464 * coeff (m + 1 + 1 + 1) G + 5760 * coeff (m + 1 + 1) G +
      2592 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 12 * X)
    (hG : G * (5 - X + (1 + X) * S) = 6 + (0) * S) :
    (-1440) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 12672 * coeff (0 + 1 + 1 + 1 + 1) G +
      9504 * coeff (0 + 1 + 1 + 1) G + 6048 * coeff (0 + 1 + 1) G +
      5040 * coeff (0 + 1) G + (-1440) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-5760) * coeff (0 + 1 + 1 + 1) G + 4464 * coeff (0 + 1 + 1) G +
      5760 * coeff (0 + 1) G + 2592 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A110521Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a110521.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 - 5 = m := rfl
  rw [e1, e2, e3, e4, e5]
  cases m with
  | zero =>
    have r := A110521Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination 6 * hG + G * (1 + PowerSeries.X) * hc)
    push_cast
    linear_combination ((-1 : ℚ) / 144) * r
  | succ m =>
    have r := A110521Aux.rel (S) G (by linear_combination hS)
        (by linear_combination 6 * hG + G * (1 + PowerSeries.X) * hc) m
    push_cast
    linear_combination ((-1 : ℚ) / 144) * r
