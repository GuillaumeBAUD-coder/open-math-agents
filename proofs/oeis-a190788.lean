import OMAStatements.S_oeis_a190788

-- Problem: A190788: Expansion of ((x-1)*sqrt(1-4*x^2))/((x-1)*sqrt(1-4*x^2)+x).
-- Upstream: formal-conjectures statements/oeis-a190788.lean:0 (declaration OMA.S_oeis_a190788.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation for G with polynomial coefficients. The recurrence is the
coefficient of a power of x in this equation, beyond the degree of its right side. -/

namespace A190788Aux

open PowerSeries

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (X + (-1 + X) * S) = 0 + (-1 + X) * S) :
    (2 * X - 6 * X ^ 2 - 12 * X ^ 3 + 48 * X ^ 4 - 8 * X ^ 5 - 88 * X ^ 6 + 96 * X ^ 7 - 32 * X ^ 8) * derivative ℚ G + (-2 + 4 * X + 4 * X ^ 2 - 8 * X ^ 3 - 8 * X ^ 4 - 16 * X ^ 5 + 64 * X ^ 6 - 32 * X ^ 7) * G = -2 + 4 * X + 6 * X ^ 2 - 8 * X ^ 3 - 8 * X ^ 4 - 24 * X ^ 5 + 64 * X ^ 6 - 32 * X ^ 7 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have hS2 : S * S = (1 - 4 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-1 + 2 * X + 4 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4) * G = (-1 + 2 * X + 3 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4 : ℚ⟦X⟧) + (-X + X ^ 2) * S := by
    linear_combination (X - (-1 + X) * S) * hG + (-1 + X) * ((-1 + X) * G - (-1 + X)) * hS
  have hPd : derivative ℚ (1 - 4 * (X * X) : ℚ⟦X⟧) = -8 * X := by
    simp [Derivation.leibniz, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-1 + 2 * X + 4 * (X * X) - 8 * (X * X * X) + 4 * (X * X * X * X) : ℚ⟦X⟧) * G) = (2 + 8 * X - 24 * X ^ 2 + 16 * X ^ 3) * G + (-1 + 2 * X + 4 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d4, d8]
    ring
  have hR : derivative ℚ ((-1 + 2 * X + 3 * (X * X) - 8 * (X * X * X) + 4 * (X * X * X * X) : ℚ⟦X⟧) + (-1 * X + 1 * (X * X) : ℚ⟦X⟧) * S) =
      2 + 6 * X - 24 * X ^ 2 + 16 * X ^ 3 + (-1 + 2 * X) * S + (-X + X ^ 2) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d3, d4, d8]
    ring
  have hk2 : (-1 + 2 * X + 4 * (X * X) - 8 * (X * X * X) + 4 * (X * X * X * X) : ℚ⟦X⟧) * G = (-1 + 2 * X + 3 * (X * X) - 8 * (X * X * X) + 4 * (X * X * X * X) : ℚ⟦X⟧) + (-1 * X + 1 * (X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (2 + 8 * X - 24 * X ^ 2 + 16 * X ^ 3) * G + (-1 + 2 * X + 4 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4) * derivative ℚ G =
      2 + 6 * X - 24 * X ^ 2 + 16 * X ^ 3 + (-1 + 2 * X) * S + (-X + X ^ 2) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (-X + X ^ 2) ^ 2 * S * hdS - 2 * (-X + X ^ 2) ^ 2 * derivative ℚ S * hS -
      (2 * (-1 + 2 * X) * (1 - 4 * X ^ 2) + (-X + X ^ 2) * (-8 * X)) * hk + 2 * (-X + X ^ 2) * (1 - 4 * X ^ 2) * hdk

theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (X + (-1 + X) * S) = 0 + (-1 + X) * S) :
    derivative ℚ G * X * C 2 + derivative ℚ G * X * X * C (-6) +
      derivative ℚ G * X * X * X * C (-12) + derivative ℚ G * X * X * X * X * C 48 +
      derivative ℚ G * X * X * X * X * X * C (-8) + derivative ℚ G * X * X * X * X * X * X * C (-88) +
      derivative ℚ G * X * X * X * X * X * X * X * C 96 + derivative ℚ G * X * X * X * X * X * X * X * X * C (-32) +
      G * C (-2) + G * X * C 4 +
      G * X * X * C 4 + G * X * X * X * C (-8) +
      G * X * X * X * X * C (-8) + G * X * X * X * X * X * C (-16) +
      G * X * X * X * X * X * X * C 64 + G * X * X * X * X * X * X * X * C (-32) =
      C (-2) + C 4 * X +
      C 6 * X * X + C (-8) * X * X * X +
      C (-8) * X * X * X * X + C (-24) * X * X * X * X * X +
      C 64 * X * X * X * X * X * X + C (-32) * X * X * X * X * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (X + (-1 + X) * S) = 0 + (-1 + X) * S) (m : ℕ) :
    2 * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-6) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-12) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 48 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-8) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-88) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      96 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-32) * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-2) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 4 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      4 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-8) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-8) * coeff (m + 1 + 1 + 1 + 1) G + (-16) * coeff (m + 1 + 1 + 1) G +
      64 * coeff (m + 1 + 1) G + (-32) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

end A190788Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a190788.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 8, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 + 1 := rfl
  have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 = m + 1 := rfl
  rw [e1, e2, e3, e4, e5, e6, e7]
  have r := A190788Aux.rel (S) G (by linear_combination hS)
      (by linear_combination hG) m
  push_cast
  linear_combination ((-1 : ℚ) / 2) * r
