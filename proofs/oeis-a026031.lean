import OMAStatements.S_oeis_a026031
import Mathlib

/-
A026031: the coefficients a(n) of A = (U + V S) / W, where S is the square root of
R = 1 - 4 * X with S(0) = 1, U = 1 - 10 * X + 36 * X ^ 2 - 56 * X ^ 3 + 34 * X ^ 4 - 4 * X ^ 5, V = -1 + 8 * X - 22 * X ^ 2 + 24 * X ^ 3 - 8 * X ^ 4, W = 2,
satisfy the stated recurrence with polynomial coefficients.

- sqrt_sq: S^2 = R, because the binomial series with exponent 1/2 squares to 1 + X and
  substitution is a ring homomorphism.
- ode: differentiating S^2 = R and multiplying by S gives 2 R S' = R' S.
- odeA: with A W = U + V S this yields the first-order equation
  2 R V W A' + (2 R V W' - (2 R V' + V R') W) A = 2 R V U' - (2 R V' + V R') U.
- For the given polynomials this equation is written out, and comparing the coefficient of
  X^m on both sides gives the recurrence, up to a rational factor.
-/

namespace OMA.P026031

open PowerSeries

lemma sqrt_sq (R : PowerSeries ℚ) (hR : constantCoeff R = 1) :
    ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)) ^ 2 = R := by
  have ha : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [hR])
  have h1 : PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) ^ 2 = 1 + X := by
    have h := binomialSeries_add (A := ℚ) (1 / 2 : ℚ) (1 / 2 : ℚ)
    have h2 := binomialSeries_nat (R := ℚ) (A := ℚ) 1
    rw [pow_two, ← h, show (1 / 2 : ℚ) + 1 / 2 = ((1 : ℕ) : ℚ) by norm_num, h2, pow_one]
  rw [← subst_pow ha, h1, subst_add ha, subst_X ha, ← coe_substAlgHom ha, map_one]
  ring

lemma ode (R S : PowerSeries ℚ) (hS : S ^ 2 = R) :
    2 * R * d⁄dX ℚ S = d⁄dX ℚ R * S := by
  have h := congrArg (d⁄dX ℚ) hS
  rw [derivative_pow] at h
  have h' : 2 * S * d⁄dX ℚ S = d⁄dX ℚ R := by simpa using h
  calc 2 * R * d⁄dX ℚ S = S * (2 * S * d⁄dX ℚ S) := by
        rw [← hS]
        ring
    _ = S * d⁄dX ℚ R := by rw [h']
    _ = d⁄dX ℚ R * S := mul_comm _ _

lemma odeA (R S U V W A : PowerSeries ℚ) (hS : S ^ 2 = R) (hA : A * W = U + V * S) :
    2 * R * V * W * d⁄dX ℚ A +
        (2 * R * V * d⁄dX ℚ W - (2 * R * d⁄dX ℚ V + V * d⁄dX ℚ R) * W) * A =
      2 * R * V * d⁄dX ℚ U - (2 * R * d⁄dX ℚ V + V * d⁄dX ℚ R) * U := by
  have h1 := ode R S hS
  have h2 := congrArg (d⁄dX ℚ) hA
  rw [Derivation.leibniz, map_add, Derivation.leibniz] at h2
  simp only [smul_eq_mul] at h2
  linear_combination (2 * R * V) * h2 + V ^ 2 * h1 - (2 * R * d⁄dX ℚ V + V * d⁄dX ℚ R) * hA

lemma d_ofNat (n : ℕ) [n.AtLeastTwo] :
    d⁄dX ℚ (no_index (OfNat.ofNat n) : ℚ⟦X⟧) = 0 := by
  rw [← map_ofNat (C (R := ℚ)) n, derivative_C]


lemma main' (R S : PowerSeries ℚ) (hR : R = 1 - 4 * X)
    (hSdef : S = (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1))
    (a : ℕ → ℚ)
    (ha : ∀ n, a n =
  coeff (n + 6)
    ((1 - 10 * X + 36 * X ^ 2 - 56 * X ^ 3 + 34 * X ^ 4 - 4 * X ^ 5 + (-1 + 8 * X - 22 * X ^ 2 + 24 * X ^ 3 - 8 * X ^ 4) * S)
      * (2 : PowerSeries ℚ)⁻¹)) :
    ∀ n : ℕ, 6 ≤ n →
    ((n : ℚ) + 6) * a n + (-10 * (n : ℚ) - 40) * a (n - 1) + (34 * (n : ℚ) + 64) * a (n - 2)
      + (-44 * (n : ℚ) + 16) * a (n - 3) + (16 * (n : ℚ) - 40) * a (n - 4) = 0 := by
  have hR1 : constantCoeff R = 1 := by
    rw [hR]
    simp [map_ofNat]
  have hS : S ^ 2 = R := by
    rw [hSdef]
    exact sqrt_sq R hR1
  obtain ⟨A, hAdef⟩ : ∃ A : PowerSeries ℚ, A = (1 - 10 * X + 36 * X ^ 2 - 56 * X ^ 3 + 34 * X ^ 4 - 4 * X ^ 5 + (-1 + 8 * X - 22 * X ^ 2 + 24 * X ^ 3 - 8 * X ^ 4) * S) * (2 : PowerSeries ℚ)⁻¹ :=
    ⟨_, rfl⟩
  have ha' : ∀ n, a n = coeff (n + 6) A := fun n => by rw [ha, hAdef]
  have hW0 : constantCoeff (2 : PowerSeries ℚ) ≠ 0 := by simp [map_ofNat]
  have hA : A * (2) = (1 - 10 * X + 36 * X ^ 2 - 56 * X ^ 3 + 34 * X ^ 4 - 4 * X ^ 5) + (-1 + 8 * X - 22 * X ^ 2 + 24 * X ^ 3 - 8 * X ^ 4) * S := by
    rw [hAdef, mul_assoc, PowerSeries.inv_mul_cancel _ hW0]
    ring
  have hode := odeA R S (1 - 10 * X + 36 * X ^ 2 - 56 * X ^ 3 + 34 * X ^ 4 - 4 * X ^ 5) (-1 + 8 * X - 22 * X ^ 2 + 24 * X ^ 3 - 8 * X ^ 4) (2) A hS hA
  have dR : d⁄dX ℚ R = -4 := by
    rw [hR]
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dU : d⁄dX ℚ (1 - 10 * X + 36 * X ^ 2 - 56 * X ^ 3 + 34 * X ^ 4 - 4 * X ^ 5 : ℚ⟦X⟧) = -10 + 72 * X - 168 * X ^ 2 + 136 * X ^ 3 - 20 * X ^ 4 := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dV : d⁄dX ℚ (-1 + 8 * X - 22 * X ^ 2 + 24 * X ^ 3 - 8 * X ^ 4 : ℚ⟦X⟧) = 8 - 44 * X + 72 * X ^ 2 - 32 * X ^ 3 := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dW : d⁄dX ℚ (2 : ℚ⟦X⟧) = 0 := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  rw [dR] at hode
  simp only [dU, dV, dW] at hode
  rw [hR] at hode
  have hg : (-1 + 2 * X : ℚ⟦X⟧) ≠ 0 := by
    intro hg0
    have h0 := congrArg constantCoeff hg0
    simp [map_ofNat] at h0
  have red : (-1 + 2 * X : ℚ⟦X⟧) * (C (4 : ℚ) * (d⁄dX ℚ A * X ^ 0) +
      C (-40 : ℚ) * (d⁄dX ℚ A * X ^ 1) +
      C (136 : ℚ) * (d⁄dX ℚ A * X ^ 2) +
      C (-176 : ℚ) * (d⁄dX ℚ A * X ^ 3) +
      C (64 : ℚ) * (d⁄dX ℚ A * X ^ 4) +
      C (40 : ℚ) * (A * X ^ 0) +
      C (-288 : ℚ) * (A * X ^ 1) +
      C (592 : ℚ) * (A * X ^ 2) +
      C (-288 : ℚ) * (A * X ^ 3)) =
      (-1 + 2 * X : ℚ⟦X⟧) * (C (32 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 7) +
      C (-64 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 8)) := by
    simp only [map_neg, map_ofNat, map_one, map_zero]
    linear_combination (1 : ℚ⟦X⟧) * hode
  have key := mul_left_cancel₀ hg red
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have tp0 : coeff (k + 11) (C (4 : ℚ) * (d⁄dX ℚ A * X ^ 0)) =
      (4 : ℚ) * (coeff (k + 12) A * ((k : ℚ) + 12)) := by
    have e : k + 11 = k + 11 + 0 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 11 + 1 = k + 12 by omega]; push_cast; ring)
  have tp1 : coeff (k + 11) (C (-40 : ℚ) * (d⁄dX ℚ A * X ^ 1)) =
      (-40 : ℚ) * (coeff (k + 11) A * ((k : ℚ) + 11)) := by
    have e : k + 11 = k + 10 + 1 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 10 + 1 = k + 11 by omega]; push_cast; ring)
  have tp2 : coeff (k + 11) (C (136 : ℚ) * (d⁄dX ℚ A * X ^ 2)) =
      (136 : ℚ) * (coeff (k + 10) A * ((k : ℚ) + 10)) := by
    have e : k + 11 = k + 9 + 2 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 9 + 1 = k + 10 by omega]; push_cast; ring)
  have tp3 : coeff (k + 11) (C (-176 : ℚ) * (d⁄dX ℚ A * X ^ 3)) =
      (-176 : ℚ) * (coeff (k + 9) A * ((k : ℚ) + 9)) := by
    have e : k + 11 = k + 8 + 3 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 8 + 1 = k + 9 by omega]; push_cast; ring)
  have tp4 : coeff (k + 11) (C (64 : ℚ) * (d⁄dX ℚ A * X ^ 4)) =
      (64 : ℚ) * (coeff (k + 8) A * ((k : ℚ) + 8)) := by
    have e : k + 11 = k + 7 + 4 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 7 + 1 = k + 8 by omega]; push_cast; ring)
  have tq0 : coeff (k + 11) (C (40 : ℚ) * (A * X ^ 0)) = (40 : ℚ) * coeff (k + 11) A := by
    have e : k + 11 = k + 11 + 0 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq1 : coeff (k + 11) (C (-288 : ℚ) * (A * X ^ 1)) = (-288 : ℚ) * coeff (k + 10) A := by
    have e : k + 11 = k + 10 + 1 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq2 : coeff (k + 11) (C (592 : ℚ) * (A * X ^ 2)) = (592 : ℚ) * coeff (k + 9) A := by
    have e : k + 11 = k + 9 + 2 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq3 : coeff (k + 11) (C (-288 : ℚ) * (A * X ^ 3)) = (-288 : ℚ) * coeff (k + 8) A := by
    have e : k + 11 = k + 8 + 3 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have th7 : coeff (k + 11) (C (32 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 7)) = 0 := by
    have e : k + 11 = k + 4 + 7 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have th8 : coeff (k + 11) (C (-64 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 8)) = 0 := by
    have e : k + 11 = k + 3 + 8 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have hc := congrArg (coeff (k + 11)) key
  simp only [map_add, map_zero, tp0, tp1, tp2, tp3, tp4, tq0, tq1, tq2, tq3, th7, th8] at hc
  have g0 : a (k + 6) = coeff (k + 12) A := by
    rw [ha', show k + 6 + 6 = k + 12 by omega]
  have g1 : a (k + 6 - 1) = coeff (k + 11) A := by
    rw [ha', show k + 6 - 1 + 6 = k + 11 by omega]
  have g2 : a (k + 6 - 2) = coeff (k + 10) A := by
    rw [ha', show k + 6 - 2 + 6 = k + 10 by omega]
  have g3 : a (k + 6 - 3) = coeff (k + 9) A := by
    rw [ha', show k + 6 - 3 + 6 = k + 9 by omega]
  have g4 : a (k + 6 - 4) = coeff (k + 8) A := by
    rw [ha', show k + 6 - 4 + 6 = k + 8 by omega]
  rw [g0, g1, g2, g3, g4]
  push_cast at hc ⊢
  linear_combination (1 / 4 : ℚ) * hc

end OMA.P026031

theorem OMA.solution : type_of% @OMA.S_oeis_a026031.main :=
  OMA.P026031.main' OMA.S_oeis_a026031.R OMA.S_oeis_a026031.S rfl rfl OMA.S_oeis_a026031.a (fun _ => rfl)
