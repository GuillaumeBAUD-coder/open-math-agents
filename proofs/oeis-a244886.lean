import OMAStatements.S_oeis_a244886

-- Problem: A244886: G.f.: (1-x+sqrt(1-2*x-3*x^2))/(1-3*x+x^2+x^3+(1-x^2)*sqrt(1-2*x-3*x^2)).
-- Upstream: formal-conjectures statements/oeis-a244886.lean:0 (declaration OMA.S_oeis_a244886.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation for G with polynomial coefficients. The recurrence is the
coefficient of a power of x in this equation, beyond the degree of its right side. -/

namespace A244886Aux

open PowerSeries

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 3 * X + X ^ 2 + X ^ 3 + (1 - X ^ 2) * S) = 1 - X + (1) * S) :
    (16 - 80 * X + 32 * X ^ 2 + 208 * X ^ 3 - 128 * X ^ 5 - 48 * X ^ 6) * derivative ℚ G + (-32 + 64 * X + 144 * X ^ 2 - 48 * X ^ 3 - 304 * X ^ 4 - 144 * X ^ 5) * G = -16 + 16 * X + 48 * X ^ 2 + 48 * X ^ 3 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have hS2 : S * S = (1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-4 * X + 16 * X ^ 2 - 8 * X ^ 3 - 12 * X ^ 4 + 4 * X ^ 5 + 4 * X ^ 6) * G = (-2 * X + 8 * X ^ 2 - 2 * X ^ 3 - 4 * X ^ 4 : ℚ⟦X⟧) + (-2 * X + 2 * X ^ 2) * S := by
    linear_combination (1 - 3 * X + X ^ 2 + X ^ 3 - (1 - X ^ 2) * S) * hG + (1 - X ^ 2) * ((1 - X ^ 2) * G - (1)) * hS
  have hPd : derivative ℚ (1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) = -2 - 6 * X := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -2 - 6 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-4 * X + 16 * (X * X) - 8 * (X * X * X) - 12 * (X * X * X * X) + 4 * (X * X * X * X * X) + 4 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-4 + 32 * X - 24 * X ^ 2 - 48 * X ^ 3 + 20 * X ^ 4 + 24 * X ^ 5) * G + (-4 * X + 16 * X ^ 2 - 8 * X ^ 3 - 12 * X ^ 4 + 4 * X ^ 5 + 4 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d8, d12, d16]
    ring
  have hR : derivative ℚ ((-2 * X + 8 * (X * X) - 2 * (X * X * X) - 4 * (X * X * X * X) : ℚ⟦X⟧) + (-2 * X + 2 * (X * X) : ℚ⟦X⟧) * S) =
      -2 + 16 * X - 6 * X ^ 2 - 16 * X ^ 3 + (-2 + 4 * X) * S + (-2 * X + 2 * X ^ 2) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d4, d8]
    ring
  have hk2 : (-4 * X + 16 * (X * X) - 8 * (X * X * X) - 12 * (X * X * X * X) + 4 * (X * X * X * X * X) + 4 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (-2 * X + 8 * (X * X) - 2 * (X * X * X) - 4 * (X * X * X * X) : ℚ⟦X⟧) + (-2 * X + 2 * (X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-4 + 32 * X - 24 * X ^ 2 - 48 * X ^ 3 + 20 * X ^ 4 + 24 * X ^ 5) * G + (-4 * X + 16 * X ^ 2 - 8 * X ^ 3 - 12 * X ^ 4 + 4 * X ^ 5 + 4 * X ^ 6) * derivative ℚ G =
      -2 + 16 * X - 6 * X ^ 2 - 16 * X ^ 3 + (-2 + 4 * X) * S + (-2 * X + 2 * X ^ 2) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 2 * ((1 - 2 * X + X ^ 2) * ((16 - 80 * X + 32 * X ^ 2 + 208 * X ^ 3 - 128 * X ^ 5 - 48 * X ^ 6) * derivative ℚ G + (-32 + 64 * X + 144 * X ^ 2 - 48 * X ^ 3 - 304 * X ^ 4 - 144 * X ^ 5) * G - (-16 + 16 * X + 48 * X ^ 2 + 48 * X ^ 3))) = 0 := by
    linear_combination (-2 * X + 2 * X ^ 2) ^ 2 * S * hdS - 2 * (-2 * X + 2 * X ^ 2) ^ 2 * derivative ℚ S * hS -
      (2 * (-2 + 4 * X) * (1 - 2 * X - 3 * X ^ 2) + (-2 * X + 2 * X ^ 2) * (-2 - 6 * X)) * hk + 2 * (-2 * X + 2 * X ^ 2) * (1 - 2 * X - 3 * X ^ 2) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 2 * X + X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 3 * X + X ^ 2 + X ^ 3 + (1 - X ^ 2) * S) = 1 - X + (1) * S) :
    derivative ℚ G * C 16 + derivative ℚ G * X * C (-80) +
      derivative ℚ G * X * X * C 32 + derivative ℚ G * X * X * X * C 208 +
      derivative ℚ G * X * X * X * X * X * C (-128) + derivative ℚ G * X * X * X * X * X * X * C (-48) +
      G * C (-32) + G * X * C 64 +
      G * X * X * C 144 + G * X * X * X * C (-48) +
      G * X * X * X * X * C (-304) + G * X * X * X * X * X * C (-144) =
      C (-16) + C 16 * X +
      C 48 * X * X + C 48 * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 3 * X + X ^ 2 + X ^ 3 + (1 - X ^ 2) * S) = 1 - X + (1) * S) (m : ℕ) :
    16 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-80) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      32 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 208 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-128) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-48) * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-32) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 64 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      144 * coeff (m + 1 + 1 + 1 + 1) G + (-48) * coeff (m + 1 + 1 + 1) G +
      (-304) * coeff (m + 1 + 1) G + (-144) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 3 * X + X ^ 2 + X ^ 3 + (1 - X ^ 2) * S) = 1 - X + (1) * S) :
    96 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-400) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      128 * coeff (0 + 1 + 1 + 1 + 1) G + 624 * coeff (0 + 1 + 1 + 1) G +
      (-128) * coeff (0 + 1) G + (-32) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      64 * coeff (0 + 1 + 1 + 1 + 1) G + 144 * coeff (0 + 1 + 1 + 1) G +
      (-48) * coeff (0 + 1 + 1) G + (-304) * coeff (0 + 1) G +
      (-144) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A244886Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a244886.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 6, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m := rfl
  rw [e1, e2, e3, e4, e5, e6]
  cases m with
  | zero =>
    have r := A244886Aux.relE0 (S) G (by linear_combination hS)
      (by linear_combination hG)
    push_cast
    linear_combination ((1 : ℚ) / 16) * r
  | succ m =>
    have r := A244886Aux.rel (S) G (by linear_combination hS)
      (by linear_combination hG) m
    push_cast
    linear_combination ((1 : ℚ) / 16) * r
