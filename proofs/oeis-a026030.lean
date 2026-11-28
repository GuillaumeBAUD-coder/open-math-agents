import OMAStatements.S_oeis_a026030
import Mathlib

/-
A026030: the coefficients a(n) of A = (U + V S) / W, where S is the square root of
R = 1 - 4 * X with S(0) = 1, U = 1 - 8 * X + 21 * X ^ 2 - 20 * X ^ 3 + 4 * X ^ 4, V = -1 + 6 * X - 11 * X ^ 2 + 6 * X ^ 3, W = 2,
satisfy the stated recurrence with polynomial coefficients.

- sqrt_sq: S^2 = R, because the binomial series with exponent 1/2 squares to 1 + X and
  substitution is a ring homomorphism.
- ode: differentiating S^2 = R and multiplying by S gives 2 R S' = R' S.
- odeA: with A W = U + V S this yields the first-order equation
  2 R V W A' + (2 R V W' - (2 R V' + V R') W) A = 2 R V U' - (2 R V' + V R') U.
- For the given polynomials this equation is written out, and comparing the coefficient of
  X^m on both sides gives the recurrence, up to a rational factor.
-/

namespace OMA.P026030

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
  coeff (n + 5)
    ((1 - 8 * X + 21 * X ^ 2 - 20 * X ^ 3 + 4 * X ^ 4 + (-1 + 6 * X - 11 * X ^ 2 + 6 * X ^ 3) * S)
      * (2 : PowerSeries ℚ)⁻¹)) :
    ∀ n : ℕ, 5 ≤ n →
    ((n : ℚ) + 5) * a n + (-10 * (n : ℚ) - 32) * a (n - 1) + (35 * (n : ℚ) + 47) * a (n - 2)
      + (-50 * (n : ℚ) + 28) * a (n - 3) + (24 * (n : ℚ) - 60) * a (n - 4) = 0 := by
  have hR1 : constantCoeff R = 1 := by
    rw [hR]
    simp [map_ofNat]
  have hS : S ^ 2 = R := by
    rw [hSdef]
    exact sqrt_sq R hR1
  obtain ⟨A, hAdef⟩ : ∃ A : PowerSeries ℚ, A = (1 - 8 * X + 21 * X ^ 2 - 20 * X ^ 3 + 4 * X ^ 4 + (-1 + 6 * X - 11 * X ^ 2 + 6 * X ^ 3) * S) * (2 : PowerSeries ℚ)⁻¹ :=
    ⟨_, rfl⟩
  have ha' : ∀ n, a n = coeff (n + 5) A := fun n => by rw [ha, hAdef]
  have hW0 : constantCoeff (2 : PowerSeries ℚ) ≠ 0 := by simp [map_ofNat]
  have hA : A * (2) = (1 - 8 * X + 21 * X ^ 2 - 20 * X ^ 3 + 4 * X ^ 4) + (-1 + 6 * X - 11 * X ^ 2 + 6 * X ^ 3) * S := by
    rw [hAdef, mul_assoc, PowerSeries.inv_mul_cancel _ hW0]
    ring
  have hode := odeA R S (1 - 8 * X + 21 * X ^ 2 - 20 * X ^ 3 + 4 * X ^ 4) (-1 + 6 * X - 11 * X ^ 2 + 6 * X ^ 3) (2) A hS hA
  have dR : d⁄dX ℚ R = -4 := by
    rw [hR]
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dU : d⁄dX ℚ (1 - 8 * X + 21 * X ^ 2 - 20 * X ^ 3 + 4 * X ^ 4 : ℚ⟦X⟧) = -8 + 42 * X - 60 * X ^ 2 + 16 * X ^ 3 := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dV : d⁄dX ℚ (-1 + 6 * X - 11 * X ^ 2 + 6 * X ^ 3 : ℚ⟦X⟧) = 6 - 22 * X + 18 * X ^ 2 := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dW : d⁄dX ℚ (2 : ℚ⟦X⟧) = 0 := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  rw [dR] at hode
  simp only [dU, dV, dW] at hode
  rw [hR] at hode
  have key : C (-4 : ℚ) * (d⁄dX ℚ A * X ^ 0) +
      C (40 : ℚ) * (d⁄dX ℚ A * X ^ 1) +
      C (-140 : ℚ) * (d⁄dX ℚ A * X ^ 2) +
      C (200 : ℚ) * (d⁄dX ℚ A * X ^ 3) +
      C (-96 : ℚ) * (d⁄dX ℚ A * X ^ 4) +
      C (-32 : ℚ) * (A * X ^ 0) +
      C (232 : ℚ) * (A * X ^ 1) +
      C (-512 : ℚ) * (A * X ^ 2) +
      C (336 : ℚ) * (A * X ^ 3) =
      C (-24 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 5) +
      C (96 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 6) +
      C (-96 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 7) := by
    simp only [map_neg, map_ofNat, map_one, map_zero]
    linear_combination (1 : ℚ⟦X⟧) * hode
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have tp0 : coeff (k + 9) (C (-4 : ℚ) * (d⁄dX ℚ A * X ^ 0)) =
      (-4 : ℚ) * (coeff (k + 10) A * ((k : ℚ) + 10)) := by
    have e : k + 9 = k + 9 + 0 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 9 + 1 = k + 10 by omega]; push_cast; ring)
  have tp1 : coeff (k + 9) (C (40 : ℚ) * (d⁄dX ℚ A * X ^ 1)) =
      (40 : ℚ) * (coeff (k + 9) A * ((k : ℚ) + 9)) := by
    have e : k + 9 = k + 8 + 1 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 8 + 1 = k + 9 by omega]; push_cast; ring)
  have tp2 : coeff (k + 9) (C (-140 : ℚ) * (d⁄dX ℚ A * X ^ 2)) =
      (-140 : ℚ) * (coeff (k + 8) A * ((k : ℚ) + 8)) := by
    have e : k + 9 = k + 7 + 2 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 7 + 1 = k + 8 by omega]; push_cast; ring)
  have tp3 : coeff (k + 9) (C (200 : ℚ) * (d⁄dX ℚ A * X ^ 3)) =
      (200 : ℚ) * (coeff (k + 7) A * ((k : ℚ) + 7)) := by
    have e : k + 9 = k + 6 + 3 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 6 + 1 = k + 7 by omega]; push_cast; ring)
  have tp4 : coeff (k + 9) (C (-96 : ℚ) * (d⁄dX ℚ A * X ^ 4)) =
      (-96 : ℚ) * (coeff (k + 6) A * ((k : ℚ) + 6)) := by
    have e : k + 9 = k + 5 + 4 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 5 + 1 = k + 6 by omega]; push_cast; ring)
  have tq0 : coeff (k + 9) (C (-32 : ℚ) * (A * X ^ 0)) = (-32 : ℚ) * coeff (k + 9) A := by
    have e : k + 9 = k + 9 + 0 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq1 : coeff (k + 9) (C (232 : ℚ) * (A * X ^ 1)) = (232 : ℚ) * coeff (k + 8) A := by
    have e : k + 9 = k + 8 + 1 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq2 : coeff (k + 9) (C (-512 : ℚ) * (A * X ^ 2)) = (-512 : ℚ) * coeff (k + 7) A := by
    have e : k + 9 = k + 7 + 2 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq3 : coeff (k + 9) (C (336 : ℚ) * (A * X ^ 3)) = (336 : ℚ) * coeff (k + 6) A := by
    have e : k + 9 = k + 6 + 3 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have th5 : coeff (k + 9) (C (-24 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 5)) = 0 := by
    have e : k + 9 = k + 4 + 5 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have th6 : coeff (k + 9) (C (96 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 6)) = 0 := by
    have e : k + 9 = k + 3 + 6 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have th7 : coeff (k + 9) (C (-96 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 7)) = 0 := by
    have e : k + 9 = k + 2 + 7 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have hc := congrArg (coeff (k + 9)) key
  simp only [map_add, map_zero, tp0, tp1, tp2, tp3, tp4, tq0, tq1, tq2, tq3, th5, th6, th7] at hc
  have g0 : a (k + 5) = coeff (k + 10) A := by
    rw [ha', show k + 5 + 5 = k + 10 by omega]
  have g1 : a (k + 5 - 1) = coeff (k + 9) A := by
    rw [ha', show k + 5 - 1 + 5 = k + 9 by omega]
  have g2 : a (k + 5 - 2) = coeff (k + 8) A := by
    rw [ha', show k + 5 - 2 + 5 = k + 8 by omega]
  have g3 : a (k + 5 - 3) = coeff (k + 7) A := by
    rw [ha', show k + 5 - 3 + 5 = k + 7 by omega]
  have g4 : a (k + 5 - 4) = coeff (k + 6) A := by
    rw [ha', show k + 5 - 4 + 5 = k + 6 by omega]
  rw [g0, g1, g2, g3, g4]
  push_cast at hc ⊢
  linear_combination (-1 / 4 : ℚ) * hc

end OMA.P026030

theorem OMA.solution : type_of% @OMA.S_oeis_a026030.main :=
  OMA.P026030.main' OMA.S_oeis_a026030.R OMA.S_oeis_a026030.S rfl rfl OMA.S_oeis_a026030.a (fun _ => rfl)
