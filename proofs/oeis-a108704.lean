import OMAStatements.S_oeis_a108704

/-!
# Proof of Mathar's recurrence for OEIS A108704

`F = exp(X^2 / 2) / sqrt(1 - 2 X)`, given as `F S = exp R` with `S^2 = 1 - 2 X` and `2 R = X^2`, and
`a(n) = n! [X^n] F`.

The series `R` has no constant term, so the chain rule gives `(exp R)' = R' exp R`. Differentiating the
three defining equations and eliminating `exp R`, `R'`, `S'` and `S` gives the differential equation
`(1 - 2 X) F' = (1 + X - 2 X^2) F` (the one recorded in the entry). The coefficient of `X^(n-1)` reads
`n f(n) - (2 n - 1) f(n-1) - f(n-2) + 2 f(n-3) = 0` for `f(n) = [X^n] F`; multiplying by `(n-1)!` gives
the recurrence. The normalisation of the square root is not needed.
-/

namespace OMA.S_oeis_a108704

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

/-- The chain rule for the exponential of a series without constant term. -/
theorem d_exp_subst (R : ℚ⟦X⟧) (hR : constantCoeff R = 0) :
    d⁄dX ℚ ((PowerSeries.exp ℚ).subst R) = (PowerSeries.exp ℚ).subst R * d⁄dX ℚ R := by
  have h := derivative_subst (f := PowerSeries.exp ℚ) (HasSubst.of_constantCoeff_zero' hR)
  have h2 : d⁄dX ℚ (PowerSeries.exp ℚ) = PowerSeries.exp ℚ := derivative_exp ℚ
  first
    | exact h.trans (congrArg (fun t : ℚ⟦X⟧ => t.subst R * d⁄dX ℚ R) h2)
    | (rw [h2] at h; exact h)
    | (simp only [h2] at h; exact h)

end OMA.S_oeis_a108704

open PowerSeries OMA.S_oeis_a108704 in
theorem OMA.solution : type_of% @OMA.S_oeis_a108704.main := by
  intro S R F hS _ hR hF n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  -- `R` has no constant term, so the chain rule applies to `E = exp R`
  have hR0 : constantCoeff R = 0 := by
    have h := congrArg constantCoeff hR
    simp only [map_mul, map_pow, map_ofNat, constantCoeff_X] at h
    norm_num at h
    exact h
  obtain ⟨E, hE⟩ : ∃ E : ℚ⟦X⟧, E = (PowerSeries.exp ℚ).subst R := ⟨_, rfl⟩
  have hE' : d⁄dX ℚ E = E * d⁄dX ℚ R := by
    rw [hE]
    exact d_exp_subst R hR0
  have hF' : F * S = E := by
    rw [hE]
    exact hF
  -- differentiate the three defining equations
  have hdS : 2 * S * d⁄dX ℚ S = -2 := by
    have h := congrArg (d⁄dX ℚ) hS
    have s1 : d⁄dX ℚ (S ^ 2) = 2 * S * d⁄dX ℚ S := by
      simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub,
        pow_one]
      ring
    have s2 : d⁄dX ℚ (1 - 2 * X : ℚ⟦X⟧) = -2 := by
      simp only [map_sub, Derivation.leibniz, Derivation.map_one_eq_zero, derivative_X, d_ofNat,
        smul_eq_mul]
      ring
    rw [s1, s2] at h
    exact h
  have hdR : 2 * d⁄dX ℚ R = 2 * X := by
    have h := congrArg (d⁄dX ℚ) hR
    have r1 : d⁄dX ℚ (2 * R) = 2 * d⁄dX ℚ R := by
      simp only [Derivation.leibniz, d_ofNat, smul_eq_mul]
      ring
    have r2 : d⁄dX ℚ (X ^ 2 : ℚ⟦X⟧) = 2 * X := by
      simp only [Derivation.leibniz_pow, derivative_X, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
        Nat.reduceSub, pow_one]
      ring
    rw [r1, r2] at h
    exact h
  have hdF : d⁄dX ℚ F * S + F * d⁄dX ℚ S = E * d⁄dX ℚ R := by
    have h := congrArg (d⁄dX ℚ) hF'
    have f1 : d⁄dX ℚ (F * S) = d⁄dX ℚ F * S + F * d⁄dX ℚ S := by
      simp only [Derivation.leibniz, smul_eq_mul]
      ring
    rw [f1, hE'] at h
    exact h
  -- the differential equation `(1 - 2 X) F' = (1 + X - 2 X ^ 2) F`, doubled
  have ode : 2 * ((1 - 2 * X) * d⁄dX ℚ F) = 2 * ((1 + X - 2 * X ^ 2) * F) := by
    linear_combination 2 * S * hdF + 2 * (X * F - d⁄dX ℚ F) * hS - F * hdS + S * E * hdR
      - 2 * X * S * hF'
  -- the same equation multiplied by `X`, written with `Θ = X F'`
  obtain ⟨Θ, hΘ, hcΘ⟩ : ∃ Θ : ℚ⟦X⟧, Θ = X * d⁄dX ℚ F ∧ ∀ k, coeff k Θ = k * coeff k F :=
    ⟨_, rfl, coeff_theta F⟩
  have key : C 2 * Θ + C 4 * (X * (X * (X * F)))
      = C 4 * (X * Θ) + C 2 * (X * F) + C 2 * (X * (X * F)) := by
    rw [hΘ]
    simp only [map_ofNat]
    linear_combination X * ode
  -- compare the coefficients of `X ^ (m + 3)`
  have h := congrArg (coeff (m + 1 + 1 + 1)) key
  simp only [map_add, coeff_C_mul, coeff_succ_X_mul, hcΘ] at h
  have i1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := by omega
  have i2 : m + 1 + 1 + 1 - 2 = m + 1 := by omega
  have i3 : m + 1 + 1 + 1 - 3 = m := by omega
  rw [i1, i2, i3]
  simp only [a]
  rw [Nat.factorial_succ (m + 1 + 1), Nat.factorial_succ (m + 1), Nat.factorial_succ m]
  push_cast at h ⊢
  linear_combination ((m : ℚ) + 2) * ((m : ℚ) + 1) * (m.factorial : ℚ) / 2 * h
