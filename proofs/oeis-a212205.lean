import OMAStatements.S_oeis_a212205

-- Problem: A212205: G.f.: ((1+2*x)*sqrt(1-6*x^2+x^4)-1+5*x^2-2*x^3)/(2*x*(1-6*x^2)).
-- Upstream: formal-conjectures statements/oeis-a212205.lean:0 (declaration OMA.S_oeis_a212205.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation for G with polynomial coefficients. The recurrence is the
coefficient of a power of x in this equation, beyond the degree of its right side. -/

namespace A212205Aux

open PowerSeries

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X ^ 2 + X ^ 4)
    (hG : G * (2 * X - 12 * X ^ 3 + (0) * S) = -1 + 5 * X ^ 2 - 2 * X ^ 3 + (1 + 2 * X) * S) :
    (4 * X + 8 * X ^ 2 - 48 * X ^ 3 - 96 * X ^ 4 + 148 * X ^ 5 + 296 * X ^ 6 - 24 * X ^ 7 - 48 * X ^ 8) * derivative ℚ G + (4 - 72 * X ^ 2 - 48 * X ^ 3 + 284 * X ^ 4 + 272 * X ^ 5 - 24 * X ^ 6) * G = 4 + 8 * X - 40 * X ^ 2 - 72 * X ^ 3 + 60 * X ^ 4 + 48 * X ^ 5 - 24 * X ^ 6 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d5 : derivative ℚ (5 : ℚ⟦X⟧) = 0 := dnum 5
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have hS2 : S * S = (1 - 6 * (X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (2 * X - 12 * X ^ 3) * G = (-1 + 5 * X ^ 2 - 2 * X ^ 3 : ℚ⟦X⟧) + (1 + 2 * X) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 6 * (X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) = -12 * X + 4 * X ^ 3 := by
    simp [Derivation.leibniz, d6]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -12 * X + 4 * X ^ 3 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((2 * X - 12 * (X * X * X) : ℚ⟦X⟧) * G) = (2 - 36 * X ^ 2) * G + (2 * X - 12 * X ^ 3) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d12]
    ring
  have hR : derivative ℚ ((-1 + 5 * (X * X) - 2 * (X * X * X) : ℚ⟦X⟧) + (1 + 2 * X : ℚ⟦X⟧) * S) =
      10 * X - 6 * X ^ 2 + (2) * S + (1 + 2 * X) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d5]
    ring
  have hk2 : (2 * X - 12 * (X * X * X) : ℚ⟦X⟧) * G = (-1 + 5 * (X * X) - 2 * (X * X * X) : ℚ⟦X⟧) + (1 + 2 * X : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (2 - 36 * X ^ 2) * G + (2 * X - 12 * X ^ 3) * derivative ℚ G =
      10 * X - 6 * X ^ 2 + (2) * S + (1 + 2 * X) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (1 + 2 * X) ^ 2 * S * hdS - 2 * (1 + 2 * X) ^ 2 * derivative ℚ S * hS -
      (2 * (2) * (1 - 6 * X ^ 2 + X ^ 4) + (1 + 2 * X) * (-12 * X + 4 * X ^ 3)) * hk + 2 * (1 + 2 * X) * (1 - 6 * X ^ 2 + X ^ 4) * hdk

theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X ^ 2 + X ^ 4)
    (hG : G * (2 * X - 12 * X ^ 3 + (0) * S) = -1 + 5 * X ^ 2 - 2 * X ^ 3 + (1 + 2 * X) * S) :
    derivative ℚ G * X * C 4 + derivative ℚ G * X * X * C 8 +
      derivative ℚ G * X * X * X * C (-48) + derivative ℚ G * X * X * X * X * C (-96) +
      derivative ℚ G * X * X * X * X * X * C 148 + derivative ℚ G * X * X * X * X * X * X * C 296 +
      derivative ℚ G * X * X * X * X * X * X * X * C (-24) + derivative ℚ G * X * X * X * X * X * X * X * X * C (-48) +
      G * C 4 + G * X * X * C (-72) +
      G * X * X * X * C (-48) + G * X * X * X * X * C 284 +
      G * X * X * X * X * X * C 272 + G * X * X * X * X * X * X * C (-24) =
      C 4 + C 8 * X +
      C (-40) * X * X + C (-72) * X * X * X +
      C 60 * X * X * X * X + C 48 * X * X * X * X * X +
      C (-24) * X * X * X * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X ^ 2 + X ^ 4)
    (hG : G * (2 * X - 12 * X ^ 3 + (0) * S) = -1 + 5 * X ^ 2 - 2 * X ^ 3 + (1 + 2 * X) * S) (m : ℕ) :
    4 * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 8 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-48) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-96) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      148 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 296 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-24) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-48) * ((m : ℚ) + 1) * coeff (m + 1) G +
      4 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-72) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-48) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 284 * coeff (m + 1 + 1 + 1 + 1) G +
      272 * coeff (m + 1 + 1 + 1) G + (-24) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X ^ 2 + X ^ 4)
    (hG : G * (2 * X - 12 * X ^ 3 + (0) * S) = -1 + 5 * X ^ 2 - 2 * X ^ 3 + (1 + 2 * X) * S) :
    28 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 48 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-240) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-384) * coeff (0 + 1 + 1 + 1 + 1) G +
      444 * coeff (0 + 1 + 1 + 1) G + 592 * coeff (0 + 1 + 1) G +
      (-24) * coeff (0 + 1) G + 4 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-72) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-48) * coeff (0 + 1 + 1 + 1 + 1) G +
      284 * coeff (0 + 1 + 1 + 1) G + 272 * coeff (0 + 1 + 1) G +
      (-24) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A212205Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a212205.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 7, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 := rfl
  have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 = m := rfl
  rw [e1, e2, e3, e4, e5, e6, e7]
  cases m with
  | zero =>
    have r := A212205Aux.relE0 (S) G (by linear_combination hS)
      (by linear_combination hG)
    push_cast
    linear_combination ((1 : ℚ) / 4) * r
  | succ m =>
    have r := A212205Aux.rel (S) G (by linear_combination hS)
      (by linear_combination hG) m
    push_cast
    linear_combination ((1 : ℚ) / 4) * r
