import OMAStatements.S_oeis_a101601

-- Problem: A101601: Expansion of g.f. c(3x)^3, where c(x) is the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a101601.lean:0 (declaration OMA.S_oeis_a101601.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A101601Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 12 * X)
    (hG : G * (216 * X ^ 3 + (0) * S) = 4 - 36 * X + (-4 + 12 * X) * S) :
    (-1728 * X + 25920 * X ^ 2 - 62208 * X ^ 3) * derivative ℚ G + (-5184 + 62208 * X - 93312 * X ^ 2) * G = -5184 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d36 : derivative ℚ (36 : ℚ⟦X⟧) = 0 := dnum 36
  have d216 : derivative ℚ (216 : ℚ⟦X⟧) = 0 := dnum 216
  have hS2 : S * S = (1 - 12 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (216 * X ^ 3) * G = (4 - 36 * X : ℚ⟦X⟧) + (-4 + 12 * X) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 12 * X : ℚ⟦X⟧) = -12 := by
    simp [Derivation.leibniz, d12]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -12 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((216 * (X * X * X) : ℚ⟦X⟧) * G) = (648 * X ^ 2) * G + (216 * X ^ 3) * derivative ℚ G := by
    simp [Derivation.leibniz, d216]
    ring
  have hR : derivative ℚ ((4 - 36 * X : ℚ⟦X⟧) + (-4 + 12 * X : ℚ⟦X⟧) * S) =
      -36 + (12) * S + (-4 + 12 * X) * derivative ℚ S := by
    simp [Derivation.leibniz, d4, d12, d36]
    ring
  have hk2 : (216 * (X * X * X) : ℚ⟦X⟧) * G = (4 - 36 * X : ℚ⟦X⟧) + (-4 + 12 * X : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (648 * X ^ 2) * G + (216 * X ^ 3) * derivative ℚ G =
      -36 + (12) * S + (-4 + 12 * X) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 2 * ((-1728 * X + 25920 * X ^ 2 - 62208 * X ^ 3) * derivative ℚ G + (-5184 + 62208 * X - 93312 * X ^ 2) * G - (-5184)) = 0 := by
    linear_combination (-4 + 12 * X) ^ 2 * S * hdS - 2 * (-4 + 12 * X) ^ 2 * derivative ℚ S * hS -
      (2 * (12) * (1 - 12 * X) + (-4 + 12 * X) * (-12)) * hk + 2 * (-4 + 12 * X) * (1 - 12 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 12 * X)
    (hG : G * (216 * X ^ 3 + (0) * S) = 4 - 36 * X + (-4 + 12 * X) * S) :
    derivative ℚ G * X * C (-1728) + derivative ℚ G * X * X * C 25920 +
      derivative ℚ G * X * X * X * C (-62208) + G * C (-5184) +
      G * X * C 62208 + G * X * X * C (-93312) =
      C (-5184) := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 12 * X)
    (hG : G * (216 * X ^ 3 + (0) * S) = 4 - 36 * X + (-4 + 12 * X) * S) (m : ℕ) :
    (-1728) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 25920 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-62208) * ((m : ℚ) + 1) * coeff (m + 1) G + (-5184) * coeff (m + 1 + 1 + 1) G +
      62208 * coeff (m + 1 + 1) G + (-93312) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 12 * X)
    (hG : G * (216 * X ^ 3 + (0) * S) = 4 - 36 * X + (-4 + 12 * X) * S) :
    (-3456) * coeff (0 + 1 + 1) G + 25920 * coeff (0 + 1) G +
      (-5184) * coeff (0 + 1 + 1) G + 62208 * coeff (0 + 1) G +
      (-93312) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A101601Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a101601.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A101601Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (216 * PowerSeries.X ^ 3) * hG - ((-1) + (2) * S + (-1) * S ^ 2 + (-6 * PowerSeries.X) * c + (6 * PowerSeries.X) * c * S + (-36 * PowerSeries.X ^ 2) * c ^ 2) * hc - ((-3) + (1) * S) * hS)
    push_cast
    linear_combination ((-1 : ℚ) / 1728) * r
  | succ m =>
    have r := A101601Aux.rel (S) G (by linear_combination hS)
        (by linear_combination (216 * PowerSeries.X ^ 3) * hG - ((-1) + (2) * S + (-1) * S ^ 2 + (-6 * PowerSeries.X) * c + (6 * PowerSeries.X) * c * S + (-36 * PowerSeries.X ^ 2) * c ^ 2) * hc - ((-3) + (1) * S) * hS) m
    push_cast
    linear_combination ((-1 : ℚ) / 1728) * r
