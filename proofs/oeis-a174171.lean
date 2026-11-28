import OMAStatements.S_oeis_a174171
import Mathlib

open OMA.S_oeis_a174171 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a174171.main := by
  intro S G hS hS0 hG n hn
  have e1 : d⁄dX ℚ (S ^ 2) = 2 * S * d⁄dX ℚ S := by
    rw [derivative_pow]; norm_num
  have e2 : d⁄dX ℚ (1 - 2 * X - 7 * X ^ 2 + 4 * X ^ 3 + 4 * X ^ 4 : ℚ⟦X⟧) =
      -2 - 14 * X + 12 * X ^ 2 + 16 * X ^ 3 := by
    rw [show (1 - 2 * X - 7 * X ^ 2 + 4 * X ^ 3 + 4 * X ^ 4 : ℚ⟦X⟧) =
      C 1 - C 2 * X - C 7 * X ^ 2 + C 4 * X ^ 3 + C 4 * X ^ 4 by simp only [map_one, map_ofNat]]
    simp only [map_add, map_sub, derivative_C, Derivation.leibniz, derivative_pow, derivative_X,
      smul_eq_mul, mul_zero, add_zero, zero_add, mul_one]
    simp only [map_ofNat, map_one]
    norm_num
    ring
  have hd := congrArg (d⁄dX ℚ) hS
  rw [e1, e2] at hd
  have ode : C 2 * d⁄dX ℚ S + C (-4) * (X ^ 1 * d⁄dX ℚ S) + C (-14) * (X ^ 2 * d⁄dX ℚ S) +
      C 8 * (X ^ 3 * d⁄dX ℚ S) + C 8 * (X ^ 4 * d⁄dX ℚ S) =
      C (-2) * S + C (-14) * (X ^ 1 * S) + C 12 * (X ^ 2 * S) + C 16 * (X ^ 3 * S) := by
    simp only [map_ofNat, map_neg, pow_one]
    linear_combination S * hd - 2 * d⁄dX ℚ S * hS
  have hgS : ∀ k : ℕ, coeff (k + 1) G * 2 = - coeff (k + 3) S := by
    intro k
    have e := congrArg (coeff (k + 3)) hG
    rw [show (2 * X ^ 2 * G : ℚ⟦X⟧) = C 2 * (X ^ 2 * G) by simp only [map_ofNat]; ring,
      show (1 - X - 2 * X ^ 2 - S : ℚ⟦X⟧) = 1 - X ^ 1 - C 2 * X ^ 2 - S by simp only [map_ofNat]; ring] at e
    simp only [map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_one] at e
    simp only [show 2 ≤ k + 3 by omega, if_true, show k + 3 - 2 = k + 1 by omega,
      show k + 3 ≠ 0 by omega, show k + 3 ≠ 1 by omega, show k + 3 ≠ 2 by omega, if_false] at e
    linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have e := congrArg (coeff (k + 5)) ode
  simp only [map_add, coeff_C_mul, coeff_derivative, coeff_X_pow_mul'] at e
  simp only [show 1 ≤ k + 5 by omega, show 2 ≤ k + 5 by omega, show 3 ≤ k + 5 by omega,
    show 4 ≤ k + 5 by omega, if_true, show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega] at e
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  have g4 := hgS (k + 3)
  have g3 := hgS (k + 2)
  have g2 := hgS (k + 1)
  have g1 := hgS k
  have g0 : (k : ℚ) * (coeff k G * 2 + coeff (k + 2) S) = 0 := by
    rcases k with _ | j
    · simp
    · have := hgS j
      rw [show j + 3 = j + 1 + 2 by ring] at this
      rw [this]; ring
  rw [show k + 3 + 1 = k + 4 by ring, show k + 3 + 3 = k + 6 by ring] at g4
  rw [show k + 2 + 1 = k + 3 by ring, show k + 2 + 3 = k + 5 by ring] at g3
  rw [show k + 1 + 1 = k + 2 by ring, show k + 1 + 3 = k + 4 by ring] at g2
  rw [show k + 5 + 1 = k + 6 by ring, show k + 4 + 1 = k + 5 by ring, show k + 3 + 1 = k + 4 by ring,
    show k + 2 + 1 = k + 3 by ring, show k + 1 + 1 = k + 2 by ring] at e
  push_cast at e ⊢
  linear_combination ((k : ℚ) + 6) / 2 * g4 - (2 * (k : ℚ) + 9) / 2 * g3 - (7 * (k : ℚ) + 21) / 2 * g2 +
    (4 * (k : ℚ) + 6) / 2 * g1 + 2 * g0 - (1 / 4 : ℚ) * e
