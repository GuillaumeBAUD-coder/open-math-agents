import OMAStatements.S_oeis_a105695

-- Problem: A105695: Expansion of (1-x)*c(x/(1+x)), where c(x) is the g.f. of the Catalan numbers (A000108).
-- Upstream: formal-conjectures statements/oeis-a105695.lean:0 (declaration OMA.S_oeis_a105695.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A105695Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (2 * X + (0) * S) = 1 - X ^ 2 + (-1 + X) * S) :
    (-4 * X + 12 * X ^ 2 + 4 * X ^ 3 - 12 * X ^ 4) * derivative ℚ G + (-4 + 4 * X + 4 * X ^ 2 + 12 * X ^ 3) * G = -4 + 4 * X + 4 * X ^ 2 - 4 * X ^ 3 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have hS2 : S * S = (1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (2 * X) * G = (1 - X ^ 2 : ℚ⟦X⟧) + (-1 + X) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) = -2 - 6 * X := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -2 - 6 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((2 * X : ℚ⟦X⟧) * G) = (2) * G + (2 * X) * derivative ℚ G := by
    simp [Derivation.leibniz, d2]
    ring
  have hR : derivative ℚ ((1 - 1 * (X * X) : ℚ⟦X⟧) + (-1 + 1 * X : ℚ⟦X⟧) * S) =
      -2 * X + (1) * S + (-1 + X) * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hk2 : (2 * X : ℚ⟦X⟧) * G = (1 - 1 * (X * X) : ℚ⟦X⟧) + (-1 + 1 * X : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (2) * G + (2 * X) * derivative ℚ G =
      -2 * X + (1) * S + (-1 + X) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (-1 + X) ^ 2 * S * hdS - 2 * (-1 + X) ^ 2 * derivative ℚ S * hS -
      (2 * (1) * (1 - 2 * X - 3 * X ^ 2) + (-1 + X) * (-2 - 6 * X)) * hk + 2 * (-1 + X) * (1 - 2 * X - 3 * X ^ 2) * hdk

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (2 * X + (0) * S) = 1 - X ^ 2 + (-1 + X) * S) :
    derivative ℚ G * X * C (-4) + derivative ℚ G * X * X * C 12 +
      derivative ℚ G * X * X * X * C 4 + derivative ℚ G * X * X * X * X * C (-12) +
      G * C (-4) + G * X * C 4 +
      G * X * X * C 4 + G * X * X * X * C 12 =
      C (-4) + C 4 * X +
      C 4 * X * X + C (-4) * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (2 * X + (0) * S) = 1 - X ^ 2 + (-1 + X) * S) (m : ℕ) :
    (-4) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 12 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      4 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-12) * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-4) * coeff (m + 1 + 1 + 1 + 1) G + 4 * coeff (m + 1 + 1 + 1) G +
      4 * coeff (m + 1 + 1) G + 12 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

end A105695Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a105695.main := by
  intro T G hT _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  rw [e1, e2, e3]
  have r := A105695Aux.rel ((1 + PowerSeries.X) * T) G (by linear_combination (1 + PowerSeries.X) * hT)
      (by linear_combination hG) m
  push_cast
  linear_combination ((-1 : ℚ) / 4) * r
