import OMAStatements.S_oeis_a097188

/-!
# Proof of Mathar's recurrence for OEIS A097188

The generating function satisfies `G * (1 - 3 X G + 3 X^2 G^2) = 1`.

Put `W = 1 - 3 X G`. The equation says `W ^ 3 = 1 - 9 X`. Differentiating gives `3 W ^ 2 W' = -9`,
and multiplying by `W` gives `(1 - 9 X) W' = -3 W`, that is
`(1 - 9 X) (G + X G') = 1 - 3 X G`. The coefficient of `X ^ m` in `X G'` is `m` times that of `G`,
so comparing the coefficients of `X ^ n` for `n ≥ 1` gives
`(n + 1) a(n) - (9 n - 3) a(n - 1) = 0`.
-/

namespace OMA.S_oeis_a097188

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

end OMA.S_oeis_a097188

open PowerSeries OMA.S_oeis_a097188 in
theorem OMA.solution : type_of% @OMA.S_oeis_a097188.main := by
  intro G hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- `W = 1 - 3 X G` satisfies `W ^ 3 = 1 - 9 X`
  have hW : (1 - 3 * X * G) ^ 3 = 1 - 9 * X := by
    linear_combination (-9 * X) * hG
  -- differentiate: `3 W ^ 2 W' = -9`, with `W' = -(3 G) - 3 X G'`
  have hdW : 3 * (1 - 3 * X * G) ^ 2 * (-(3 * G) - 3 * X * d⁄dX ℚ G) = -9 := by
    have h := congrArg (d⁄dX ℚ) hW
    have e1 : d⁄dX ℚ ((1 - 3 * X * G) ^ 3)
        = 3 * (1 - 3 * X * G) ^ 2 * (-(3 * G) - 3 * X * d⁄dX ℚ G) := by
      simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_one_eq_zero,
        derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub]
      ring
    have e2 : d⁄dX ℚ (1 - 9 * X : ℚ⟦X⟧) = -9 := by
      simp only [map_sub, Derivation.leibniz, Derivation.map_one_eq_zero, derivative_X, d_ofNat,
        smul_eq_mul]
      ring
    rw [e1, e2] at h
    exact h
  -- the differential equation `(1 - 9 X) (G + X G') = 1 - 3 X G`, written with `Θ = X G'`
  obtain ⟨Θ, hΘ, hcΘ⟩ : ∃ Θ : ℚ⟦X⟧, Θ = X * d⁄dX ℚ G ∧ ∀ k, coeff k Θ = k * coeff k G :=
    ⟨_, rfl, coeff_theta G⟩
  have key : C 9 * (G + Θ + C 3 * (X * G)) = C 9 * (1 + C 9 * (X * G) + C 9 * (X * Θ)) := by
    rw [hΘ]
    simp only [map_ofNat]
    linear_combination (-(1 - 3 * X * G)) * hdW + 3 * (-(3 * G) - 3 * X * d⁄dX ℚ G) * hW
  -- compare the coefficients of `X ^ (m + 1)`
  have hne : m + 1 ≠ 0 := by omega
  have h := congrArg (coeff (m + 1)) key
  simp only [coeff_C_mul, map_add, coeff_succ_X_mul, hcΘ, coeff_one, if_neg hne] at h
  have e : m + 1 - 1 = m := by omega
  rw [e]
  push_cast at h ⊢
  linear_combination (1 / 9 : ℚ) * h
