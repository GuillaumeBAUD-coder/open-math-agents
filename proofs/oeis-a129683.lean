import OMAStatements.S_oeis_a129683

/-!
# Proof of Mathar's recurrence for OEIS A129683

`F = exp(R) / (1 - 2 X)` with `R = 2 X / (1 - 2 X)`, and `a(n) = n! [X^n] F`.

The series `R` has no constant term, so the chain rule gives `(exp R)' = R' exp R`. Differentiating
`R (1 - 2 X) = 2 X` and `F (1 - 2 X) = exp R` and eliminating `exp R` and `R'` gives the differential
equation `(1 - 2 X)^2 F' = (4 - 4 X) F`. The coefficient of `X^(n-1)` reads
`n f(n) - 4 n f(n-1) + 4 (n - 1) f(n-2) = 0` for `f(n) = [X^n] F`; multiplying by `(n-1)!` gives the
recurrence.
-/

namespace OMA.S_oeis_a129683

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

end OMA.S_oeis_a129683

open PowerSeries OMA.S_oeis_a129683 in
theorem OMA.solution : type_of% @OMA.S_oeis_a129683.main := by
  intro R F hR hF n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  -- `R` has no constant term, so the chain rule applies to `E = exp R`
  have hR0 : constantCoeff R = 0 := by
    have h := congrArg constantCoeff hR
    simp only [map_mul, map_sub, map_one, map_ofNat, constantCoeff_X] at h
    norm_num at h
    exact h
  obtain ⟨E, hE⟩ : ∃ E : ℚ⟦X⟧, E = (PowerSeries.exp ℚ).subst R := ⟨_, rfl⟩
  have hE' : d⁄dX ℚ E = E * d⁄dX ℚ R := by
    rw [hE]
    exact d_exp_subst R hR0
  have hF' : F * (1 - 2 * X) = (1) * E := by
    rw [hE]
    exact hF
  -- differentiate the two defining equations
  have e1 : ∀ f : ℚ⟦X⟧, d⁄dX ℚ (f * (1 - 2 * X)) = d⁄dX ℚ f * (1 - 2 * X) - 2 * f := by
    intro f
    simp only [map_sub, Derivation.leibniz, Derivation.map_one_eq_zero, derivative_X, d_ofNat,
      smul_eq_mul]
    ring
  have hdR : d⁄dX ℚ R * (1 - 2 * X) - 2 * R = 2 := by
    have h := congrArg (d⁄dX ℚ) hR
    have e3 : d⁄dX ℚ (2 * X : ℚ⟦X⟧) = 2 := by
      simp only [Derivation.leibniz, derivative_X, d_ofNat, smul_eq_mul]
      ring
    rw [e1, e3] at h
    exact h
  have hdF : d⁄dX ℚ F * (1 - 2 * X) - 2 * F = E * d⁄dX ℚ R := by
    have h := congrArg (d⁄dX ℚ) hF'
    rw [e1, one_mul, hE'] at h
    exact h
  -- the differential equation `(1 - 2 X) ^ 2 F' = (4 - 4 X) F`
  have ode : (1 - 2 * X) ^ 2 * d⁄dX ℚ F = (4 - 4 * X) * F := by
    linear_combination (1 - 2 * X) * hdF + E * hdR + 2 * F * hR - (2 * R + 2) * hF'
  -- the same equation multiplied by `X`, written with `Θ = X F'`
  obtain ⟨Θ, hΘ, hcΘ⟩ : ∃ Θ : ℚ⟦X⟧, Θ = X * d⁄dX ℚ F ∧ ∀ k, coeff k Θ = k * coeff k F :=
    ⟨_, rfl, coeff_theta F⟩
  have key : Θ + C 4 * (X * (X * Θ)) + C 4 * (X * (X * F))
      = C 4 * (X * Θ) + C 4 * (X * F) := by
    rw [hΘ]
    simp only [map_ofNat]
    linear_combination X * ode
  -- compare the coefficients of `X ^ (m + 2)`
  have h := congrArg (coeff (m + 1 + 1)) key
  simp only [map_add, coeff_C_mul, coeff_succ_X_mul, hcΘ] at h
  have i1 : m + 1 + 1 - 1 = m + 1 := by omega
  have i2 : m + 1 + 1 - 2 = m := by omega
  rw [i1, i2]
  simp only [a]
  rw [Nat.factorial_succ (m + 1), Nat.factorial_succ m]
  push_cast at h ⊢
  linear_combination ((m : ℚ) + 1) * (m.factorial : ℚ) * h
