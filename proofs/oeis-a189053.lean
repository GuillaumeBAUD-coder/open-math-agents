import OMAStatements.S_oeis_a189053

/-!
# Proof of the recurrence for OEIS A189053

With `S ^ 2 = 1 - 4 * X ^ 2`, the generating function satisfies
`G * (1 - 17 * X ^ 2 + 108 * X ^ 4 - 304 * X ^ 6 + 320 * X ^ 8) = X - 8 * X ^ 3 + 16 * X ^ 5 + (1 - 8 * X ^ 2 + 16 * X ^ 4) * S`.

Differentiating `S ^ 2 = p` gives `2 p S' = p' S`. Differentiating the equation for `G`, and using it
to eliminate `S'` and then `S`, gives a first-order linear differential equation with polynomial
coefficients; after cancelling a common factor it reads
`(1 + X - 13 * X ^ 2 - 13 * X ^ 3 + 56 * X ^ 4 + 56 * X ^ 5 - 80 * X ^ 6 - 80 * X ^ 7) * (X G') + (-14 * X ^ 2 - 14 * X ^ 3 + 116 * X ^ 4 + 116 * X ^ 5 - 240 * X ^ 6 - 240 * X ^ 7) * G = X + X ^ 2`.
The coefficient of `X ^ m` in `X G'` is `m` times that of `G`, so comparing the coefficients of
`X ^ n` for `n ≥ 7` gives the recurrence.
-/

namespace OMA.S_oeis_a189053

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

end OMA.S_oeis_a189053

set_option maxHeartbeats 1600000 in
open PowerSeries OMA.S_oeis_a189053 in
theorem OMA.solution : type_of% @OMA.S_oeis_a189053.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 7, by omega⟩
  have hS' : S ^ 2 = 1 - 4 * X ^ 2 := by
    linear_combination hS
  have h1 : G * (1 - 17 * X ^ 2 + 108 * X ^ 4 - 304 * X ^ 6 + 320 * X ^ 8) = X - 8 * X ^ 3 + 16 * X ^ 5 + (1 - 8 * X ^ 2 + 16 * X ^ 4) * S := by
    linear_combination ((1 - 8 * X ^ 2 + 16 * X ^ 4) - (-X + 4 * X ^ 3) * S) * hG + (G * (-X + 4 * X ^ 3) ^ 2 - (1) * (-X + 4 * X ^ 3)) * hS
  have hdS : 2 * S * d⁄dX ℚ S = -8 * X := by
    have h := congrArg (d⁄dX ℚ) hS'
    have e1 : d⁄dX ℚ (S ^ 2) = 2 * S * d⁄dX ℚ S := by
      simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub,
        pow_one]
      ring
    have e2 : d⁄dX ℚ (1 - 4 * X ^ 2 : ℚ⟦X⟧) = -8 * X := by
      simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
        Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
        Nat.reduceSub, pow_one]
      ring
    rw [e1, e2] at h
    exact h
  have hdS2 : 2 * (1 - 4 * X ^ 2) * d⁄dX ℚ S = (-8 * X) * S := by
    linear_combination S * hdS - 2 * d⁄dX ℚ S * hS'
  have hE : d⁄dX ℚ G * (1 - 17 * X ^ 2 + 108 * X ^ 4 - 304 * X ^ 6 + 320 * X ^ 8) + G * (-34 * X + 432 * X ^ 3 - 1824 * X ^ 5 + 2560 * X ^ 7) = 1 - 24 * X ^ 2 + 80 * X ^ 4 + (-16 * X + 64 * X ^ 3) * S + (1 - 8 * X ^ 2 + 16 * X ^ 4) * d⁄dX ℚ S := by
    have h := congrArg (d⁄dX ℚ) h1
    have e1 : d⁄dX ℚ (G * (1 - 17 * X ^ 2 + 108 * X ^ 4 - 304 * X ^ 6 + 320 * X ^ 8)) = d⁄dX ℚ G * (1 - 17 * X ^ 2 + 108 * X ^ 4 - 304 * X ^ 6 + 320 * X ^ 8) + G * (-34 * X + 432 * X ^ 3 - 1824 * X ^ 5 + 2560 * X ^ 7) := by
      simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
        Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
        Nat.reduceSub, pow_one]
      ring
    have e2 : d⁄dX ℚ (X - 8 * X ^ 3 + 16 * X ^ 5 + (1 - 8 * X ^ 2 + 16 * X ^ 4) * S) = 1 - 24 * X ^ 2 + 80 * X ^ 4 + (-16 * X + 64 * X ^ 3) * S + (1 - 8 * X ^ 2 + 16 * X ^ 4) * d⁄dX ℚ S := by
      simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
        Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
        Nat.reduceSub, pow_one]
      ring
    rw [e1, e2] at h
    exact h
  have key : (-2 + 32 * X ^ 2 - 192 * X ^ 4 + 512 * X ^ 6 - 512 * X ^ 8) * ((1 + X - 13 * X ^ 2 - 13 * X ^ 3 + 56 * X ^ 4 + 56 * X ^ 5 - 80 * X ^ 6 - 80 * X ^ 7) * (X * d⁄dX ℚ G) + (-14 * X ^ 2 - 14 * X ^ 3 + 116 * X ^ 4 + 116 * X ^ 5 - 240 * X ^ 6 - 240 * X ^ 7) * G - (X + X ^ 2)) = 0 := by
    linear_combination ((-1 - X) * X * (2 * (1 - 4 * X ^ 2) * (1 - 8 * X ^ 2 + 16 * X ^ 4))) * hE + ((-1 - X) * X * (1 - 8 * X ^ 2 + 16 * X ^ 4) ^ 2) * hdS2
      - ((-1 - X) * X * (2 * (1 - 4 * X ^ 2) * (-16 * X + 64 * X ^ 3) + (1 - 8 * X ^ 2 + 16 * X ^ 4) * (-8 * X))) * h1
  have hF : (-2 + 32 * X ^ 2 - 192 * X ^ 4 + 512 * X ^ 6 - 512 * X ^ 8 : ℚ⟦X⟧) ≠ 0 := by
    have hrw : (-2 + 32 * X ^ 2 - 192 * X ^ 4 + 512 * X ^ 6 - 512 * X ^ 8 : ℚ⟦X⟧) = C (-2) + X * (32 * X - 192 * X ^ 3 + 512 * X ^ 5 - 512 * X ^ 7) := by
      simp only [map_ofNat, map_neg, map_one]
      ring
    rw [hrw]
    intro h
    have h0 := congrArg (coeff 0) h
    simp only [map_add, coeff_zero_C, coeff_zero_X_mul, map_zero, add_zero] at h0
    norm_num at h0
  have ode : (1 + X - 13 * X ^ 2 - 13 * X ^ 3 + 56 * X ^ 4 + 56 * X ^ 5 - 80 * X ^ 6 - 80 * X ^ 7) * (X * d⁄dX ℚ G) + (-14 * X ^ 2 - 14 * X ^ 3 + 116 * X ^ 4 + 116 * X ^ 5 - 240 * X ^ 6 - 240 * X ^ 7) * G - (X + X ^ 2) = 0 :=
    (mul_eq_zero.mp key).resolve_left (hF)
  obtain ⟨Θ, hΘ, hcΘ⟩ : ∃ Θ : ℚ⟦X⟧, Θ = X * d⁄dX ℚ G ∧ ∀ k, coeff k Θ = k * coeff k G :=
    ⟨_, rfl, coeff_theta G⟩
  have key2 : C (1) * Θ
      + C (1) * (X * Θ)
      + C (-13) * (X * (X * Θ))
      + C (-13) * (X * (X * (X * Θ)))
      + C (56) * (X * (X * (X * (X * Θ))))
      + C (56) * (X * (X * (X * (X * (X * Θ)))))
      + C (-80) * (X * (X * (X * (X * (X * (X * Θ))))))
      + C (-80) * (X * (X * (X * (X * (X * (X * (X * Θ)))))))
      + C (-14) * (X * (X * G))
      + C (-14) * (X * (X * (X * G)))
      + C (116) * (X * (X * (X * (X * G))))
      + C (116) * (X * (X * (X * (X * (X * G)))))
      + C (-240) * (X * (X * (X * (X * (X * (X * G))))))
      + C (-240) * (X * (X * (X * (X * (X * (X * (X * G)))))))
      + C (-1) * (X * 1)
      + C (-1) * (X * (X * 1)) = 0 := by
    rw [hΘ]
    simp only [map_ofNat, map_neg, map_one]
    linear_combination ode
  have hne1 : m + 1 ≠ 0 := by omega
  have hne2 : m + 1 + 1 ≠ 0 := by omega
  have hne3 : m + 1 + 1 + 1 ≠ 0 := by omega
  have hne4 : m + 1 + 1 + 1 + 1 ≠ 0 := by omega
  have hne5 : m + 1 + 1 + 1 + 1 + 1 ≠ 0 := by omega
  have hne6 : m + 1 + 1 + 1 + 1 + 1 + 1 ≠ 0 := by omega
  have hne7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 0 := by omega
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) key2
  simp only [map_add, coeff_C_mul, coeff_succ_X_mul, hcΘ, coeff_one, map_zero, if_neg hne1, if_neg hne2, if_neg hne3, if_neg hne4, if_neg hne5, if_neg hne6, if_neg hne7] at h
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 := by omega
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 := by omega
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 := by omega
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 := by omega
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 := by omega
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 := by omega
  have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 = m := by omega
  rw [e1, e2, e3, e4, e5, e6, e7]
  push_cast at h ⊢
  linear_combination (1 / 1 : ℚ) * h
