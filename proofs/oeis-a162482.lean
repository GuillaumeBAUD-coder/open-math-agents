import OMAStatements.S_oeis_a162482

-- Problem: A162482: Expansion of (1/(1-x)^3)*M(x/(1-x)^3), M(x) the g.f. of Motzkin numbers A001006.
-- Upstream: formal-conjectures statements/oeis-a162482.lean:0 (declaration OMA.S_oeis_a162482.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A162482Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X + 18 * X ^ 2 - 26 * X ^ 3 + 17 * X ^ 4 - 6 * X ^ 5 + X ^ 6)
    (hG : G * (2 * X ^ 2 + (0) * S) = 1 - 4 * X + 3 * X ^ 2 - X ^ 3 + (-1) * S) :
    (-4 * X + 32 * X ^ 2 - 72 * X ^ 3 + 104 * X ^ 4 - 68 * X ^ 5 + 24 * X ^ 6 - 4 * X ^ 7) * derivative ℚ G + (-8 + 48 * X - 72 * X ^ 2 + 52 * X ^ 3 - 12 * X ^ 5 + 4 * X ^ 6) * G = -8 + 24 * X ^ 2 - 16 * X ^ 3 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d17 : derivative ℚ (17 : ℚ⟦X⟧) = 0 := dnum 17
  have d18 : derivative ℚ (18 : ℚ⟦X⟧) = 0 := dnum 18
  have d26 : derivative ℚ (26 : ℚ⟦X⟧) = 0 := dnum 26
  have hS2 : S * S = (1 - 8 * X + 18 * (X * X) - 26 * (X * X * X) + 17 * (X * X * X * X) - 6 * (X * X * X * X * X) + 1 * (X * X * X * X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (2 * X ^ 2) * G = (1 - 4 * X + 3 * X ^ 2 - X ^ 3 : ℚ⟦X⟧) + (-1) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 8 * X + 18 * (X * X) - 26 * (X * X * X) + 17 * (X * X * X * X) - 6 * (X * X * X * X * X) + 1 * (X * X * X * X * X * X) : ℚ⟦X⟧) = -8 + 36 * X - 78 * X ^ 2 + 68 * X ^ 3 - 30 * X ^ 4 + 6 * X ^ 5 := by
    simp [Derivation.leibniz, d6, d8, d17, d18, d26]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 + 36 * X - 78 * X ^ 2 + 68 * X ^ 3 - 30 * X ^ 4 + 6 * X ^ 5 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((2 * (X * X) : ℚ⟦X⟧) * G) = (4 * X) * G + (2 * X ^ 2) * derivative ℚ G := by
    simp [Derivation.leibniz, d2]
    ring
  have hR : derivative ℚ ((1 - 4 * X + 3 * (X * X) - 1 * (X * X * X) : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S) =
      -4 + 6 * X - 3 * X ^ 2 + (0) * S + (-1) * derivative ℚ S := by
    simp [Derivation.leibniz, d3, d4]
    ring
  have hk2 : (2 * (X * X) : ℚ⟦X⟧) * G = (1 - 4 * X + 3 * (X * X) - 1 * (X * X * X) : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (4 * X) * G + (2 * X ^ 2) * derivative ℚ G =
      -4 + 6 * X - 3 * X ^ 2 + (0) * S + (-1) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 1 * ((-4 * X + 32 * X ^ 2 - 72 * X ^ 3 + 104 * X ^ 4 - 68 * X ^ 5 + 24 * X ^ 6 - 4 * X ^ 7) * derivative ℚ G + (-8 + 48 * X - 72 * X ^ 2 + 52 * X ^ 3 - 12 * X ^ 5 + 4 * X ^ 6) * G - (-8 + 24 * X ^ 2 - 16 * X ^ 3)) = 0 := by
    linear_combination (-1) ^ 2 * S * hdS - 2 * (-1) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 - 8 * X + 18 * X ^ 2 - 26 * X ^ 3 + 17 * X ^ 4 - 6 * X ^ 5 + X ^ 6) + (-1) * (-8 + 36 * X - 78 * X ^ 2 + 68 * X ^ 3 - 30 * X ^ 4 + 6 * X ^ 5)) * hk + 2 * (-1) * (1 - 8 * X + 18 * X ^ 2 - 26 * X ^ 3 + 17 * X ^ 4 - 6 * X ^ 5 + X ^ 6) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 1 ≠ 0 := pow_ne_zero 1 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X + 18 * X ^ 2 - 26 * X ^ 3 + 17 * X ^ 4 - 6 * X ^ 5 + X ^ 6)
    (hG : G * (2 * X ^ 2 + (0) * S) = 1 - 4 * X + 3 * X ^ 2 - X ^ 3 + (-1) * S) :
    derivative ℚ G * X * C (-4) + derivative ℚ G * X * X * C 32 +
      derivative ℚ G * X * X * X * C (-72) + derivative ℚ G * X * X * X * X * C 104 +
      derivative ℚ G * X * X * X * X * X * C (-68) + derivative ℚ G * X * X * X * X * X * X * C 24 +
      derivative ℚ G * X * X * X * X * X * X * X * C (-4) + G * C (-8) +
      G * X * C 48 + G * X * X * C (-72) +
      G * X * X * X * C 52 + G * X * X * X * X * X * C (-12) +
      G * X * X * X * X * X * X * C 4 =
      C (-8) + C 24 * X * X +
      C (-16) * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X + 18 * X ^ 2 - 26 * X ^ 3 + 17 * X ^ 4 - 6 * X ^ 5 + X ^ 6)
    (hG : G * (2 * X ^ 2 + (0) * S) = 1 - 4 * X + 3 * X ^ 2 - X ^ 3 + (-1) * S) (m : ℕ) :
    (-4) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 32 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-72) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 104 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-68) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 24 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-4) * ((m : ℚ) + 1) * coeff (m + 1) G + (-8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      48 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-72) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      52 * coeff (m + 1 + 1 + 1 + 1) G + (-12) * coeff (m + 1 + 1) G +
      4 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X + 18 * X ^ 2 - 26 * X ^ 3 + 17 * X ^ 4 - 6 * X ^ 5 + X ^ 6)
    (hG : G * (2 * X ^ 2 + (0) * S) = 1 - 4 * X + 3 * X ^ 2 - X ^ 3 + (-1) * S) :
    (-24) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 160 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-288) * coeff (0 + 1 + 1 + 1 + 1) G + 312 * coeff (0 + 1 + 1 + 1) G +
      (-136) * coeff (0 + 1 + 1) G + 24 * coeff (0 + 1) G +
      (-8) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 48 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-72) * coeff (0 + 1 + 1 + 1 + 1) G + 52 * coeff (0 + 1 + 1 + 1) G +
      (-12) * coeff (0 + 1) G + 4 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A162482Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a162482.main := by
  intro T G hT _ hG n hn
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
    have r := A162482Aux.relE0 ((1 - PowerSeries.X) ^ 3 * T) G (by linear_combination hT)
        (by linear_combination hG)
    push_cast
    linear_combination ((-1 : ℚ) / 4) * r
  | succ m =>
    have r := A162482Aux.rel ((1 - PowerSeries.X) ^ 3 * T) G (by linear_combination hT)
        (by linear_combination hG) m
    push_cast
    linear_combination ((-1 : ℚ) / 4) * r
