import OMAStatements.S_oeis_a166587
import Mathlib

namespace OMA.A166587Proof

open PowerSeries

/-- The g.f. satisfies x(1+2x-3x^2)G' + (1+x)G = 1 + 3x. -/
theorem ode (S G : ℚ⟦X⟧) (h1 : S ^ 2 = 1 + 2 * X - 3 * X ^ 2) (h2 : 2 * X * G = 1 + 3 * X - S) :
    X * (1 + 2 * X - 3 * X ^ 2) * d⁄dX ℚ G + (1 + X) * G = 1 + 3 * X := by
  have hS : S = 1 + 3 * X - 2 * X * G := by linear_combination h2
  subst hS
  have hd := congrArg (d⁄dX ℚ) h1
  have hX2 : d⁄dX ℚ ((X : ℚ⟦X⟧) ^ 2) = 2 * X := by
    rw [Derivation.leibniz_pow]
    simp [smul_eq_mul]
  have h3 : d⁄dX ℚ (3 * X : ℚ⟦X⟧) = 3 := by
    rw [show (3 * X : ℚ⟦X⟧) = X + X + X by ring, map_add, map_add, derivative_X]
    norm_num
  have h2' : d⁄dX ℚ (2 * X : ℚ⟦X⟧) = 2 := by
    rw [show (2 * X : ℚ⟦X⟧) = X + X by ring, map_add, derivative_X]
    norm_num
  have h3X2 : d⁄dX ℚ (3 * X ^ 2 : ℚ⟦X⟧) = 6 * X := by
    rw [show (3 * X ^ 2 : ℚ⟦X⟧) = X ^ 2 + X ^ 2 + X ^ 2 by ring, map_add, map_add, hX2]
    ring
  have h2XG : d⁄dX ℚ (2 * X * G : ℚ⟦X⟧) = 2 * G + 2 * X * d⁄dX ℚ G := by
    rw [Derivation.leibniz, h2', smul_eq_mul, smul_eq_mul]
    ring
  rw [Derivation.leibniz_pow] at hd
  simp only [map_add, map_sub, Derivation.map_one_eq_zero, h3, h2', h3X2, h2XG, smul_eq_mul]
    at hd
  -- hd : 2 * S * S' = 2 - 6X, with S = 1 + 3X - 2XG
  have h4 : (2 : ℚ⟦X⟧) * (1 + 3 * X - 2 * X * G) ^ 2 * (3 - (2 * G + 2 * X * d⁄dX ℚ G)) =
      (2 - 6 * X) * (1 + 3 * X - 2 * X * G) := by
    have e : ((2 - 1 : ℕ) : ℚ⟦X⟧) = 1 := by norm_num
    linear_combination (1 + 3 * X - 2 * X * G) * hd
  have h5 := h4
  rw [h1] at h5
  have h4' : (4 : ℚ⟦X⟧) * (X * (1 + 2 * X - 3 * X ^ 2) * d⁄dX ℚ G + (1 + X) * G - (1 + 3 * X)) = 0 := by
    linear_combination -h5
  have h4n : (4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h0 := congrArg (coeff 0) h
    rw [show (4 : ℚ⟦X⟧) = C 4 from (map_ofNat C 4).symm, coeff_C] at h0
    norm_num at h0
  have := (mul_eq_zero.1 h4').resolve_left h4n
  linear_combination this

/-- Coefficient form: (m+3) g(m+2) + (2m+3) g(m+1) - 3m g(m) = 0. -/
theorem rec3 (S G : ℚ⟦X⟧) (h1 : S ^ 2 = 1 + 2 * X - 3 * X ^ 2) (h2 : 2 * X * G = 1 + 3 * X - S)
    (m : ℕ) :
    ((m : ℚ) + 3) * coeff (m + 2) G + (2 * (m : ℚ) + 3) * coeff (m + 1) G
      - 3 * (m : ℚ) * coeff m G = 0 := by
  have h := congrArg (coeff (m + 2)) (ode S G h1 h2)
  have hL : X * (1 + 2 * X - 3 * X ^ 2) * d⁄dX ℚ G + (1 + X) * G =
      d⁄dX ℚ G * X ^ 1 + C 2 * (d⁄dX ℚ G * X ^ 2) - C 3 * (d⁄dX ℚ G * X ^ 3) + G + G * X ^ 1 := by
    simp only [map_ofNat]; ring
  have hR : (1 + 3 * X : ℚ⟦X⟧) = C 1 + C 3 * X ^ 1 := by
    simp only [map_ofNat, map_one]; ring
  rw [hL, hR] at h
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_derivative, coeff_C,
    if_pos (show 1 ≤ m + 2 by omega), if_pos (show 2 ≤ m + 2 by omega),
    show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
    if_neg (show m + 2 ≠ 0 by omega)] at h
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp at h
    push_cast at h ⊢
    linear_combination h
  · simp only [if_pos (show 3 ≤ m + 2 by omega), show m + 2 - 3 = m - 1 by omega,
      show m - 1 + 1 = m by omega] at h
    have hc : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by rw [Nat.cast_sub hm]; simp
    rw [hc] at h
    push_cast at h
    linear_combination h

end OMA.A166587Proof

open OMA.A166587Proof PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a166587.main := by
  intro S G h1 _ h2 n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have r1 := rec3 S G h1 h2 (k + 1)
  have r0 := rec3 S G h1 h2 k
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  simp only [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at r1
  push_cast at r1 ⊢
  linear_combination ((k : ℚ) + 3) * r1 - ((k : ℚ) + 1) * r0
