import OMAStatements.S_oeis_a174783

-- Problem: A174783: Expansion of (1+2x-sqrt(1-4x^2))/(2(1-x^2)*sqrt(1-4x^2)).
-- Upstream: formal-conjectures statements/oeis-a174783.lean:0 (declaration OMA.S_oeis_a174783.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A174783Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (0 + (2 - 2 * X ^ 2) * S) = 1 + 2 * X + (-1) * S) :
    (16 - 80 * X ^ 2 + 64 * X ^ 4) * derivative ℚ G + (-32 - 32 * X + 32 * X ^ 2 + 128 * X ^ 3) * G = 16 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d10 : derivative ℚ (10 : ℚ⟦X⟧) = 0 := dnum 10
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d36 : derivative ℚ (36 : ℚ⟦X⟧) = 0 := dnum 36
  have hS2 : S * S = (1 - 4 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-4 + 24 * X ^ 2 - 36 * X ^ 4 + 16 * X ^ 6) * G = (2 - 10 * X ^ 2 + 8 * X ^ 4 : ℚ⟦X⟧) + (-2 - 4 * X + 2 * X ^ 2 + 4 * X ^ 3) * S := by
    linear_combination (0 - (2 - 2 * X ^ 2) * S) * hG + (2 - 2 * X ^ 2) * ((2 - 2 * X ^ 2) * G - (-1)) * hS
  have hPd : derivative ℚ (1 - 4 * (X * X) : ℚ⟦X⟧) = -8 * X := by
    simp [Derivation.leibniz, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-4 + 24 * (X * X) - 36 * (X * X * X * X) + 16 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (48 * X - 144 * X ^ 3 + 96 * X ^ 5) * G + (-4 + 24 * X ^ 2 - 36 * X ^ 4 + 16 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d16, d24, d36]
    ring
  have hR : derivative ℚ ((2 - 10 * (X * X) + 8 * (X * X * X * X) : ℚ⟦X⟧) + (-2 - 4 * X + 2 * (X * X) + 4 * (X * X * X) : ℚ⟦X⟧) * S) =
      -20 * X + 32 * X ^ 3 + (-4 + 4 * X + 12 * X ^ 2) * S + (-2 - 4 * X + 2 * X ^ 2 + 4 * X ^ 3) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d4, d8, d10]
    ring
  have hk2 : (-4 + 24 * (X * X) - 36 * (X * X * X * X) + 16 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (2 - 10 * (X * X) + 8 * (X * X * X * X) : ℚ⟦X⟧) + (-2 - 4 * X + 2 * (X * X) + 4 * (X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (48 * X - 144 * X ^ 3 + 96 * X ^ 5) * G + (-4 + 24 * X ^ 2 - 36 * X ^ 4 + 16 * X ^ 6) * derivative ℚ G =
      -20 * X + 32 * X ^ 3 + (-4 + 4 * X + 12 * X ^ 2) * S + (-2 - 4 * X + 2 * X ^ 2 + 4 * X ^ 3) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 + 2 * X - 6 * X ^ 2 - 12 * X ^ 3 + 9 * X ^ 4 + 18 * X ^ 5 - 4 * X ^ 6 - 8 * X ^ 7) * ((16 - 80 * X ^ 2 + 64 * X ^ 4) * derivative ℚ G + (-32 - 32 * X + 32 * X ^ 2 + 128 * X ^ 3) * G - (16)) = 0 := by
    linear_combination (-2 - 4 * X + 2 * X ^ 2 + 4 * X ^ 3) ^ 2 * S * hdS - 2 * (-2 - 4 * X + 2 * X ^ 2 + 4 * X ^ 3) ^ 2 * derivative ℚ S * hS -
      (2 * (-4 + 4 * X + 12 * X ^ 2) * (1 - 4 * X ^ 2) + (-2 - 4 * X + 2 * X ^ 2 + 4 * X ^ 3) * (-8 * X)) * hk + 2 * (-2 - 4 * X + 2 * X ^ 2 + 4 * X ^ 3) * (1 - 4 * X ^ 2) * hdk
  have hg : (1 + 2 * X - 6 * X ^ 2 - 12 * X ^ 3 + 9 * X ^ 4 + 18 * X ^ 5 - 4 * X ^ 6 - 8 * X ^ 7 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (0 + (2 - 2 * X ^ 2) * S) = 1 + 2 * X + (-1) * S) :
    derivative ℚ G * C 16 + derivative ℚ G * X * X * C (-80) +
      derivative ℚ G * X * X * X * X * C 64 + G * C (-32) +
      G * X * C (-32) + G * X * X * C 32 +
      G * X * X * X * C 128 =
      C 16 := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (0 + (2 - 2 * X ^ 2) * S) = 1 + 2 * X + (-1) * S) (m : ℕ) :
    16 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-80) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      64 * ((m : ℚ) + 1) * coeff (m + 1) G + (-32) * coeff (m + 1 + 1 + 1 + 1) G +
      (-32) * coeff (m + 1 + 1 + 1) G + 32 * coeff (m + 1 + 1) G +
      128 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (0 + (2 - 2 * X ^ 2) * S) = 1 + 2 * X + (-1) * S) :
    64 * coeff (0 + 1 + 1 + 1 + 1) G + (-160) * coeff (0 + 1 + 1) G +
      (-32) * coeff (0 + 1 + 1 + 1) G + (-32) * coeff (0 + 1 + 1) G +
      32 * coeff (0 + 1) G + 128 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A174783Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a174783.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  cases m with
  | zero =>
    have r := A174783Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination ((1 : ℚ) / 16) * r
  | succ m =>
    have r := A174783Aux.rel (S) G (by linear_combination hS)
        (by linear_combination hG) m
    push_cast
    linear_combination ((1 : ℚ) / 16) * r
