import OMAStatements.S_oeis_a276068

/-!
# Proof of the recurrence for OEIS A276068

With `S ^ 2 = 1 - 4 * X + 2 * X ^ 2 + X ^ 4`, the generating function satisfies
`G * (2 * X - 4 * X ^ 2) = 1 - 3 * X + X ^ 2 + X ^ 3 + (-1 + X) * S`.

Differentiating `S ^ 2 = p` gives `2 p S' = p' S`. Differentiating the equation for `G`, and using it
to eliminate `S'` and then `S`, gives a first-order linear differential equation with polynomial
coefficients; after cancelling a common factor it reads
`(1 - 6 * X + 10 * X ^ 2 - 4 * X ^ 3 + X ^ 4 - 2 * X ^ 5) * (X G') + (1 - 5 * X + 7 * X ^ 2 + X ^ 3 + 2 * X ^ 5) * G = 3 * X ^ 2 - 5 * X ^ 3 + 3 * X ^ 4 - X ^ 5`.
The coefficient of `X ^ m` in `X G'` is `m` times that of `G`, so comparing the coefficients of
`X ^ n` for `n ≥ 6` gives the recurrence.
-/

namespace OMA.S_oeis_a276068

open PowerSeries

/-- Numerals are constants for the derivative. -/
theorem d_ofNat (n : ℕ) [n.AtLeastTwo] : d⁄dX ℚ (ofNat(n) : ℚ⟦X⟧) = 0 := by
  first
    | exact Derivation.map_natCast (d⁄dX ℚ) n
    | (rw [← map_ofNat (C : ℚ →+* ℚ⟦X⟧) n]; exact derivative_C)

/-- The coefficient of `X ^ m` in `X * f'` is `m` times the coefficient of `X ^ m` in `f`. -/
theorem coeff_theta (f : ℚ⟦X⟧) (m : ℕ) : coeff m (X * d⁄dX ℚ f) = m * coeff m f := by
  cases m with
  | zero => simp
  | succ m =>
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

end OMA.S_oeis_a276068

set_option maxHeartbeats 1600000 in
open PowerSeries OMA.S_oeis_a276068 in
theorem OMA.solution : type_of% @OMA.S_oeis_a276068.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 6, by omega⟩
  have hS' : S ^ 2 = 1 - 4 * X + 2 * X ^ 2 + X ^ 4 := by
    linear_combination hS
  have h1 : G * (2 * X - 4 * X ^ 2) = 1 - 3 * X + X ^ 2 + X ^ 3 + (-1 + X) * S := by
    linear_combination hG
  have hdS : 2 * S * d⁄dX ℚ S = -4 + 4 * X + 4 * X ^ 3 := by
    have h := congrArg (d⁄dX ℚ) hS'
    have e1 : d⁄dX ℚ (S ^ 2) = 2 * S * d⁄dX ℚ S := by
      simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub,
        pow_one]
      ring
    have e2 : d⁄dX ℚ (1 - 4 * X + 2 * X ^ 2 + X ^ 4 : ℚ⟦X⟧) = -4 + 4 * X + 4 * X ^ 3 := by
      simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
        Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
        Nat.reduceSub, pow_one]
      ring
    rw [e1, e2] at h
    exact h
  have hdS2 : 2 * (1 - 4 * X + 2 * X ^ 2 + X ^ 4) * d⁄dX ℚ S = (-4 + 4 * X + 4 * X ^ 3) * S := by
    linear_combination S * hdS - 2 * d⁄dX ℚ S * hS'
  have hE : d⁄dX ℚ G * (2 * X - 4 * X ^ 2) + G * (2 - 8 * X) = -3 + 2 * X + 3 * X ^ 2 + (1) * S + (-1 + X) * d⁄dX ℚ S := by
    have h := congrArg (d⁄dX ℚ) h1
    have e1 : d⁄dX ℚ (G * (2 * X - 4 * X ^ 2)) = d⁄dX ℚ G * (2 * X - 4 * X ^ 2) + G * (2 - 8 * X) := by
      simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
        Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
        Nat.reduceSub, pow_one]
      ring
    have e2 : d⁄dX ℚ (1 - 3 * X + X ^ 2 + X ^ 3 + (-1 + X) * S) = -3 + 2 * X + 3 * X ^ 2 + (1) * S + (-1 + X) * d⁄dX ℚ S := by
      simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
        Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
        Nat.reduceSub, pow_one]
      ring
    rw [e1, e2] at h
    exact h
  have key : X * (4 - 4 * X) * ((1 - 6 * X + 10 * X ^ 2 - 4 * X ^ 3 + X ^ 4 - 2 * X ^ 5) * (X * d⁄dX ℚ G) + (1 - 5 * X + 7 * X ^ 2 + X ^ 3 + 2 * X ^ 5) * G - (3 * X ^ 2 - 5 * X ^ 3 + 3 * X ^ 4 - X ^ 5)) = 0 := by
    linear_combination ((-1) * X * (2 * (1 - 4 * X + 2 * X ^ 2 + X ^ 4) * (-1 + X))) * hE + ((-1) * X * (-1 + X) ^ 2) * hdS2
      - ((-1) * X * (2 * (1 - 4 * X + 2 * X ^ 2 + X ^ 4) * (1) + (-1 + X) * (-4 + 4 * X + 4 * X ^ 3))) * h1
  have hF : (4 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
    have hrw : (4 - 4 * X : ℚ⟦X⟧) = C (4) + X * (-4) := by
      simp only [map_ofNat, map_neg, map_one]
      ring
    rw [hrw]
    intro h
    have h0 := congrArg (coeff 0) h
    simp only [map_add, coeff_zero_C, coeff_zero_X_mul, map_zero, add_zero] at h0
    norm_num at h0
  have ode : (1 - 6 * X + 10 * X ^ 2 - 4 * X ^ 3 + X ^ 4 - 2 * X ^ 5) * (X * d⁄dX ℚ G) + (1 - 5 * X + 7 * X ^ 2 + X ^ 3 + 2 * X ^ 5) * G - (3 * X ^ 2 - 5 * X ^ 3 + 3 * X ^ 4 - X ^ 5) = 0 :=
    (mul_eq_zero.mp key).resolve_left (mul_ne_zero (X_ne_zero) hF)
  obtain ⟨Θ, hΘ, hcΘ⟩ : ∃ Θ : ℚ⟦X⟧, Θ = X * d⁄dX ℚ G ∧ ∀ k, coeff k Θ = k * coeff k G :=
    ⟨_, rfl, coeff_theta G⟩
  have key2 : C (1) * Θ
      + C (-6) * (X * Θ)
      + C (10) * (X * (X * Θ))
      + C (-4) * (X * (X * (X * Θ)))
      + C (1) * (X * (X * (X * (X * Θ))))
      + C (-2) * (X * (X * (X * (X * (X * Θ)))))
      + C (1) * G
      + C (-5) * (X * G)
      + C (7) * (X * (X * G))
      + C (1) * (X * (X * (X * G)))
      + C (2) * (X * (X * (X * (X * (X * G)))))
      + C (-3) * (X * (X * 1))
      + C (5) * (X * (X * (X * 1)))
      + C (-3) * (X * (X * (X * (X * 1))))
      + C (1) * (X * (X * (X * (X * (X * 1))))) = 0 := by
    rw [hΘ]
    simp only [map_ofNat, map_neg, map_one]
    linear_combination ode
  have hne1 : m + 1 ≠ 0 := by omega
  have hne2 : m + 1 + 1 ≠ 0 := by omega
  have hne3 : m + 1 + 1 + 1 ≠ 0 := by omega
  have hne4 : m + 1 + 1 + 1 + 1 ≠ 0 := by omega
  have hne5 : m + 1 + 1 + 1 + 1 + 1 ≠ 0 := by omega
  have hne6 : m + 1 + 1 + 1 + 1 + 1 + 1 ≠ 0 := by omega
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) key2
  simp only [map_add, coeff_C_mul, coeff_succ_X_mul, hcΘ, coeff_one, map_zero, if_neg hne1, if_neg hne2, if_neg hne3, if_neg hne4, if_neg hne5, if_neg hne6] at h
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 := by omega
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 := by omega
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 := by omega
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 := by omega
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 := by omega
  rw [e1, e2, e3, e4, e5]
  push_cast at h ⊢
  linear_combination (1 / 1 : ℚ) * h
