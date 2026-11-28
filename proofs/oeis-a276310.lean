import OMAStatements.S_oeis_a276310

/-!
# Proof of Mathar's recurrence for OEIS A276310

The generating function is the power series `G` with zero constant term and
`X = G - 2 G ^ 2 - 2 G ^ 3`.

Put `F = 1 - 4 G - 6 G ^ 2`. Differentiating the equation once and twice gives `G' F = 1` and
`G'' F = (4 + 12 G) G' ^ 2`, hence `F ^ 3 G' = F ^ 2` and `F ^ 3 G'' = 4 + 12 G`. Substituting these
and `X = G - 2 G ^ 2 - 2 G ^ 3` into
`(3 - 26 X - 27 X ^ 2) (X G' + X ^ 2 G'') + (-3 + 13 X) X G' + 3 X ^ 2 G + X ^ 2`
times `F ^ 3` gives a polynomial in `G` that vanishes identically; since `F` has constant term `1`,
the expression itself is zero. The coefficient of `X ^ m` in `X G'` is `m` times that of `G`, and
in `X ^ 2 G''` it is `m (m - 1)` times that of `G`, so comparing the coefficients of `X ^ n` for
`n ≥ 3` gives the recurrence.
-/

namespace OMA.S_oeis_a276310

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

/-- The coefficient of `X ^ m` in `X ^ 2 * f''` is `m * (m - 1)` times that of `f`. -/
theorem coeff_theta2 (f : ℚ⟦X⟧) (m : ℕ) :
    coeff m (X * (X * d⁄dX ℚ (d⁄dX ℚ f))) = (m : ℚ) * ((m : ℚ) - 1) * coeff m f := by
  rcases m with _ | _ | m
  · simp
  · rw [coeff_succ_X_mul, coeff_zero_X_mul]
    push_cast
    ring
  · rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_derivative, coeff_derivative]
    push_cast
    ring

end OMA.S_oeis_a276310

set_option maxHeartbeats 1600000 in
open PowerSeries OMA.S_oeis_a276310 in
theorem OMA.solution : type_of% @OMA.S_oeis_a276310.main := by
  intro G hG0 hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  -- first and second derivative of `X = G - 2 G ^ 2 - 2 G ^ 3`
  have h1 : d⁄dX ℚ G * (1 - 4 * G - 6 * G ^ 2) = 1 := by
    have h := congrArg (d⁄dX ℚ) hG
    have e2 : d⁄dX ℚ (G - 2 * G ^ 2 - 2 * G ^ 3) = d⁄dX ℚ G * (1 - 4 * G - 6 * G ^ 2) := by
      simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow, d_ofNat, smul_eq_mul,
        nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      ring
    rw [derivative_X, e2] at h
    exact h.symm
  have h2 : d⁄dX ℚ (d⁄dX ℚ G) * (1 - 4 * G - 6 * G ^ 2) - (4 + 12 * G) * d⁄dX ℚ G ^ 2 = 0 := by
    have h := congrArg (d⁄dX ℚ) h1
    have e1 : d⁄dX ℚ (d⁄dX ℚ G * (1 - 4 * G - 6 * G ^ 2))
        = d⁄dX ℚ (d⁄dX ℚ G) * (1 - 4 * G - 6 * G ^ 2) - (4 + 12 * G) * d⁄dX ℚ G ^ 2 := by
      simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_one_eq_zero,
        d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      ring
    rw [e1, Derivation.map_one_eq_zero] at h
    exact h
  -- clear the denominators: `F ^ 3 G' = F ^ 2` and `F ^ 3 G'' = 4 + 12 G`, with `F = 1 - 4 G - 6 G ^ 2`
  have eA : (1 - 4 * G - 6 * G ^ 2) ^ 3 * d⁄dX ℚ G = (1 - 4 * G - 6 * G ^ 2) ^ 2 := by
    linear_combination (1 - 4 * G - 6 * G ^ 2) ^ 2 * h1
  have eB : (1 - 4 * G - 6 * G ^ 2) ^ 3 * d⁄dX ℚ (d⁄dX ℚ G) = 4 + 12 * G := by
    linear_combination (1 - 4 * G - 6 * G ^ 2) ^ 2 * h2 + (4 + 12 * G) * (d⁄dX ℚ G * (1 - 4 * G - 6 * G ^ 2) + 1) * h1
  -- the differential equation, first with `G - 2 G ^ 2 - 2 G ^ 3` in place of `X`
  have key : (1 - 4 * G - 6 * G ^ 2) ^ 3 * ((3 - 26 * (G - 2 * G ^ 2 - 2 * G ^ 3) - 27 * (G - 2 * G ^ 2 - 2 * G ^ 3) ^ 2) * ((G - 2 * G ^ 2 - 2 * G ^ 3) * d⁄dX ℚ G + (G - 2 * G ^ 2 - 2 * G ^ 3) ^ 2 * d⁄dX ℚ (d⁄dX ℚ G))
        + (-3 + 13 * (G - 2 * G ^ 2 - 2 * G ^ 3)) * ((G - 2 * G ^ 2 - 2 * G ^ 3) * d⁄dX ℚ G) + 3 * (G - 2 * G ^ 2 - 2 * G ^ 3) ^ 2 * G + (G - 2 * G ^ 2 - 2 * G ^ 3) ^ 2) = 0 := by
    linear_combination ((3 - 26 * (G - 2 * G ^ 2 - 2 * G ^ 3) - 27 * (G - 2 * G ^ 2 - 2 * G ^ 3) ^ 2) * (G - 2 * G ^ 2 - 2 * G ^ 3) + (-3 + 13 * (G - 2 * G ^ 2 - 2 * G ^ 3)) * (G - 2 * G ^ 2 - 2 * G ^ 3)) * eA
      + ((3 - 26 * (G - 2 * G ^ 2 - 2 * G ^ 3) - 27 * (G - 2 * G ^ 2 - 2 * G ^ 3) ^ 2) * (G - 2 * G ^ 2 - 2 * G ^ 3) ^ 2) * eB
  rw [← hG] at key
  have hc0 : constantCoeff G = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hG0
  have hF : ((1 - 4 * G - 6 * G ^ 2) : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h0 := congrArg (coeff 0) h
    norm_num [hc0] at h0
  have ode : (3 - 26 * X - 27 * X ^ 2) * (X * d⁄dX ℚ G + X ^ 2 * d⁄dX ℚ (d⁄dX ℚ G))
        + (-3 + 13 * X) * (X * d⁄dX ℚ G) + 3 * X ^ 2 * G + X ^ 2 = 0 :=
    (mul_eq_zero.mp key).resolve_left (pow_ne_zero 3 hF)
  obtain ⟨Θ, hΘ, hcΘ⟩ : ∃ Θ : ℚ⟦X⟧, Θ = X * d⁄dX ℚ G ∧ ∀ k, coeff k Θ = k * coeff k G :=
    ⟨_, rfl, coeff_theta G⟩
  obtain ⟨W, hW, hcW⟩ : ∃ W : ℚ⟦X⟧, W = X * (X * d⁄dX ℚ (d⁄dX ℚ G)) ∧
      ∀ k : ℕ, coeff k W = (k : ℚ) * ((k : ℚ) - 1) * coeff k G :=
    ⟨_, rfl, coeff_theta2 G⟩
  have key2 : C (3) * Θ + C (-26) * (X * Θ) + C (-27) * (X * (X * Θ))
      + C (3) * W + C (-26) * (X * W) + C (-27) * (X * (X * W))
      + C (-3) * Θ + C (13) * (X * Θ)
      + C (3) * (X * (X * G))
      + C (1) * (X * (X * 1)) = 0 := by
    rw [hΘ, hW]
    simp only [map_ofNat, map_neg, map_one]
    linear_combination ode
  have hne1 : m + 1 ≠ 0 := by omega
  have hne2 : m + 1 + 1 ≠ 0 := by omega
  have hne3 : m + 1 + 1 + 1 ≠ 0 := by omega
  have h := congrArg (coeff (m + 1 + 1 + 1)) key2
  simp only [map_add, coeff_C_mul, coeff_succ_X_mul, hcΘ, hcW, coeff_one, map_zero, if_neg hne1,
    if_neg hne2, if_neg hne3] at h
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := by omega
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := by omega
  rw [e1, e2]
  push_cast at h ⊢
  linear_combination h
