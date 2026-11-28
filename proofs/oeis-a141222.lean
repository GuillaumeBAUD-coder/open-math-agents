import OMAStatements.S_oeis_a141222

-- Problem: A141222: Expansion of -1/(2x) + (2x-1)^2/(2x(1-4x)^(3/2)).
-- Upstream: formal-conjectures statements/oeis-a141222.lean:0 (declaration OMA.S_oeis_a141222.main)
-- Credit: @thatoneguy006 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Mathar's recurrence holds for n >= 2 exactly when
D = (1 - 8X + 4X^2) G + X (1 - 2X)(1 - 4X) G' has no terms of degree >= 2.
Differentiating S^2 = 1 - 4X gives S S' = -2, and differentiating the defining equation of G
gives an equation for G'. With P = 2X(1 - 4X)S, the product (D - (1 + 2X)) P^2 is an explicit
linear combination of these four identities, so D = 1 + 2X because the power series ring over
Q is a domain and P is nonzero. Reading off the coefficient of X^n gives the recurrence.
-/

open PowerSeries

namespace A141222P

lemma d_ofNat (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k : ℚ⟦X⟧) = 0 := by
  rw [show (OfNat.ofNat k : ℚ⟦X⟧) = C (OfNat.ofNat k : ℚ) from (map_ofNat C k).symm]
  exact derivative_C

theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X) (h0 : coeff 0 S = 1)
    (hG : G * (2 * X * ((1 - 4 * X) * S)) = (2 * X - 1) ^ 2 - (1 - 4 * X) * S) :
    (1 - 8 * X + 4 * X ^ 2) * G + X * (1 - 2 * X) * (1 - 4 * X) * d⁄dX ℚ G = 1 + 2 * X := by
  have d2 : d⁄dX ℚ (2 : ℚ⟦X⟧) = 0 := d_ofNat 2
  have d4 : d⁄dX ℚ (4 : ℚ⟦X⟧) = 0 := d_ofNat 4
  have h1 := congrArg (d⁄dX ℚ) hS
  have h4 := congrArg (d⁄dX ℚ) hG
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, derivative_X,
    derivative_one, smul_eq_mul, d2, d4, nsmul_eq_mul] at h1 h4
  push_cast at h1 h4
  set dS := d⁄dX ℚ S
  set dG := d⁄dX ℚ G
  have two : (2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' : (C (2 : ℚ) : ℚ⟦X⟧) = 0 := (map_ofNat C 2).trans h
    have := congrArg (coeff 0) h'
    rw [coeff_zero_C, map_zero] at this
    norm_num at this
  have h2 : S * dS = -2 := by
    refine mul_left_cancel₀ two ?_
    linear_combination h1
  have hP : (2 * X * ((1 - 4 * X) * S) : ℚ⟦X⟧) ≠ 0 := by
    have hX : (X : ℚ⟦X⟧) ≠ 0 := X_ne_zero
    have h14 : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
      intro h
      have := congrArg (coeff 0) h
      simp at this
    have hS0 : S ≠ 0 := by
      intro h; rw [h] at h0; simp at h0
    exact mul_ne_zero (mul_ne_zero two hX) (mul_ne_zero h14 hS0)
  have hD : ((1 - 8 * X + 4 * X ^ 2) * G + X * (1 - 2 * X) * (1 - 4 * X) * dG)
      * (2 * X * ((1 - 4 * X) * S)) ^ 2
      = (1 + 2 * X) * (2 * X * ((1 - 4 * X) * S)) ^ 2 := by
    linear_combination
      (96*S*X^4 - 40*S*X^3 + 4*S*X^2 + 64*dS*X^5 - 64*dS*X^4 + 20*dS*X^3 - 2*dS*X^2) * hG
      + (-64*S*X^5 + 64*S*X^4 - 20*S*X^3 + 2*S*X^2) * h4
      + (64*dS*X^6 - 112*dS*X^5 + 72*dS*X^4 - 20*dS*X^3 + 2*dS*X^2) * hS
      + (-64*S*X^6 + 112*S*X^5 - 72*S*X^4 + 20*S*X^3 - 2*S*X^2) * h2
  exact mul_right_cancel₀ (pow_ne_zero 2 hP) hD

lemma coeff_X_mul_deriv (f : ℚ⟦X⟧) (k : ℕ) :
    coeff k (X * d⁄dX ℚ f) = (k : ℚ) * coeff k f := by
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast; ring

theorem final : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    G * (2 * X * ((1 - 4 * X) * S)) = (2 * X - 1) ^ 2 - (1 - 4 * X) * S →
    ∀ n : ℕ, 2 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (-2 - 6 * (n : ℚ)) * coeff (n - 1) G +
        (-12 + 8 * (n : ℚ)) * coeff (n - 2) G = 0 := by
  intro S G hS h0 hG n hn
  have hk := key S G hS h0 hG
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hform : (1 - 8 * X + 4 * X ^ 2) * G + X * (1 - 2 * X) * (1 - 4 * X) * d⁄dX ℚ G
      = G - C 8 * (X * G) + C 4 * (X ^ 2 * G) + X * d⁄dX ℚ G
        - C 6 * (X * (X * d⁄dX ℚ G)) + C 8 * (X ^ 2 * (X * d⁄dX ℚ G)) := by
    simp only [map_ofNat]; ring
  have hr : (1 + 2 * X : ℚ⟦X⟧) = 1 + C 2 * X := by simp only [map_ofNat]
  rw [hform, hr] at hk
  have hc := congrArg (coeff (m + 2)) hk
  have e1 : coeff (m + 2) (X * G) = coeff (m + 1) G := coeff_succ_X_mul (m + 1) G
  have e2 : coeff (m + 2) (X ^ 2 * G) = coeff m G := coeff_X_pow_mul G 2 m
  have e3 : coeff (m + 2) (X * (X * d⁄dX ℚ G)) = coeff (m + 1) (X * d⁄dX ℚ G) :=
    coeff_succ_X_mul (m + 1) _
  have e4 : coeff (m + 2) (X ^ 2 * (X * d⁄dX ℚ G)) = coeff m (X * d⁄dX ℚ G) :=
    coeff_X_pow_mul _ 2 m
  have e5 : coeff (m + 2) (C 2 * X : ℚ⟦X⟧) = 0 := by
    rw [coeff_C_mul, coeff_X]; simp
  have e6 : coeff (m + 2) (1 : ℚ⟦X⟧) = 0 := by rw [coeff_one]; simp
  simp only [map_add, map_sub, coeff_C_mul, e1, e2, e3, e4, e5, e6, coeff_X_mul_deriv] at hc
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  push_cast at hc ⊢
  linear_combination hc

end A141222P

theorem OMA.solution : type_of% @OMA.S_oeis_a141222.main := by
  exact A141222P.final
