import OMAStatements.S_oeis_a215973
import Mathlib

/-
A215973: a sequence defined by a convolution recurrence satisfies the stated recurrence with
polynomial coefficients.

Let A be the generating function with rational coefficients.
- hFE: the defining recurrence says (X - X ^ 2) A^2 + (-1 + 2 * X) A + (1 - X) = 0, checked coefficient by
  coefficient (the convolution sum is the coefficient of A^2).
- Then S = 2 (X - X ^ 2) A + (-1 + 2 * X) satisfies S^2 = R with R = 1 - 8 * X + 12 * X ^ 2 - 4 * X ^ 3.
- ode, odeA: differentiating S^2 = R gives 2 R S' = R' S, hence a first-order linear equation
  for A with polynomial coefficients; a common polynomial factor is cancelled.
- Comparing the coefficient of X^m on both sides gives the recurrence, up to a rational factor.
-/

namespace OMA.P215973

open PowerSeries

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


lemma main' (a : ℕ → ℤ) (h0 : a 0 = 1)
    (hrec : ∀ n, a (n + 1) = ∑ k : Fin (n + 1), a k * (1 + a (n - k))) :
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℤ) + 1) * a n + 3 * (-3 * (n : ℤ) + 1) * a (n - 1) + 4 * (5 * (n : ℤ) - 7) * a (n - 2)
      + 2 * (-8 * (n : ℤ) + 19) * a (n - 3) + 2 * (2 * (n : ℤ) - 7) * a (n - 4) = 0 := by
  obtain ⟨A, hAdef⟩ : ∃ A : ℚ⟦X⟧, A = PowerSeries.mk (fun n => (a n : ℚ)) := ⟨_, rfl⟩
  have hcA : ∀ n, coeff n A = (a n : ℚ) := fun n => by rw [hAdef, coeff_mk]
  have hcc : constantCoeff A = (a 0 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply, hcA]
  have hconv : ∀ m, coeff m (A ^ 2) =
      ∑ k ∈ Finset.range (m + 1), (a k : ℚ) * (a (m - k) : ℚ) := by
    intro m
    rw [pow_two, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i A * coeff j A)]
    simp only [hcA]
  have e0 : ∀ n, (∑ k : Fin (n + 1), (a k : ℚ) * (a (n - k) : ℚ)) =
      ∑ k ∈ Finset.range (n + 1), (a k : ℚ) * (a (n - k) : ℚ) := fun n =>
    Fin.sum_univ_eq_sum_range (fun k => (a k : ℚ) * (a (n - k) : ℚ)) (n + 1)
  have e1 : ∀ n, (∑ k : Fin (n + 2), (a k : ℚ) * (a (n + 1 - k) : ℚ)) =
      ∑ k ∈ Finset.range (n + 1 + 1), (a k : ℚ) * (a (n + 1 - k) : ℚ) := fun n =>
    Fin.sum_univ_eq_sum_range (fun k => (a k : ℚ) * (a (n + 1 - k) : ℚ)) (n + 2)
  have hrecQ : ∀ n, coeff (n + 1) A = ((∑ k ∈ Finset.range (n + 1), coeff k A) + coeff n (A ^ 2)) := by
    intro n
    simp only [hcA, hconv]
    rw [hrec n]
    push_cast
    simp only [mul_add, mul_one, Finset.sum_add_distrib, e0]
    rw [Fin.sum_univ_eq_sum_range (fun k => (a k : ℚ)) (n + 1)]
  have hFE : C (1 : ℚ) * (A ^ 2 * X ^ 1) +
      C (-1 : ℚ) * (A ^ 2 * X ^ 2) +
      C (-1 : ℚ) * (A * X ^ 0) +
      C (2 : ℚ) * (A * X ^ 1) +
      C (1 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 0) +
      C (-1 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 1) = 0 := by
    ext m
    rcases m with _ | _ | k
    · simp [coeff_C_mul, coeff_mul_X_pow', coeff_one, hcA, hcc, hconv, h0, Finset.sum_range_succ, hrec] <;> norm_num
    · simp [coeff_C_mul, coeff_mul_X_pow', coeff_one, hcA, hcc, hconv, h0, Finset.sum_range_succ, hrec] <;> norm_num
    · have fa1 : coeff (k + 1 + 1) (C (1 : ℚ) * (A ^ 2 * X ^ 1)) = (1 : ℚ) * coeff (k + 1) (A ^ 2) := by
        have e : k + 1 + 1 = k + 1 + 1 := by omega
        conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
      have fa2 : coeff (k + 1 + 1) (C (-1 : ℚ) * (A ^ 2 * X ^ 2)) = (-1 : ℚ) * coeff (k) (A ^ 2) := by
        have e : k + 1 + 1 = k + 2 := by omega
        conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
      have fb0 : coeff (k + 1 + 1) (C (-1 : ℚ) * (A * X ^ 0)) = (-1 : ℚ) * coeff (k + 2) (A) := by
        have e : k + 1 + 1 = k + 2 + 0 := by omega
        conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
      have fb1 : coeff (k + 1 + 1) (C (2 : ℚ) * (A * X ^ 1)) = (2 : ℚ) * coeff (k + 1) (A) := by
        have e : k + 1 + 1 = k + 1 + 1 := by omega
        conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
      have fg0 : coeff (k + 1 + 1) (C (1 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 0)) = 0 := by
        have e : k + 1 + 1 = k + 2 + 0 := by omega
        rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
      have fg1 : coeff (k + 1 + 1) (C (-1 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 1)) = 0 := by
        have e : k + 1 + 1 = k + 1 + 1 := by omega
        rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
      simp only [map_add, map_zero, fa1, fa2, fb0, fb1, fg0, fg1]
      have hs := Finset.sum_range_succ (fun j => coeff j A) (k + 1)
      linear_combination (-1 : ℚ) * hrecQ (k + 1) + hrecQ k - hs
  have hFE' : (X - X ^ 2) * A ^ 2 + (-1 + 2 * X) * A + (1 - X) = 0 := by
    simp only [map_neg, map_ofNat, map_one, map_zero] at hFE
    linear_combination hFE
  obtain ⟨S, hSdef⟩ : ∃ S : ℚ⟦X⟧, S = 2 * (X - X ^ 2) * A + (-1 + 2 * X) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℚ⟦X⟧, R = 1 - 8 * X + 12 * X ^ 2 - 4 * X ^ 3 := ⟨_, rfl⟩
  have hS : S ^ 2 = R := by
    rw [hSdef, hR]
    linear_combination (4 * (X - X ^ 2)) * hFE'
  have hA : A * (2 * X - 2 * X ^ 2) = (1 - 2 * X) + (1) * S := by
    rw [hSdef]
    ring
  have hode := odeA R S (1 - 2 * X) (1) (2 * X - 2 * X ^ 2) A hS hA
  have dR : d⁄dX ℚ R = -8 + 24 * X - 12 * X ^ 2 := by
    rw [hR]
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dU : d⁄dX ℚ (1 - 2 * X : ℚ⟦X⟧) = -2 := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dV : d⁄dX ℚ (1 : ℚ⟦X⟧) = 0 := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dW : d⁄dX ℚ (2 * X - 2 * X ^ 2 : ℚ⟦X⟧) = 2 - 4 * X := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  rw [dR] at hode
  simp only [dU, dV, dW] at hode
  rw [hR] at hode
  have key : C (4 : ℚ) * (d⁄dX ℚ A * X ^ 1) +
      C (-36 : ℚ) * (d⁄dX ℚ A * X ^ 2) +
      C (80 : ℚ) * (d⁄dX ℚ A * X ^ 3) +
      C (-64 : ℚ) * (d⁄dX ℚ A * X ^ 4) +
      C (16 : ℚ) * (d⁄dX ℚ A * X ^ 5) +
      C (4 : ℚ) * (A * X ^ 0) +
      C (-24 : ℚ) * (A * X ^ 1) +
      C (48 : ℚ) * (A * X ^ 2) +
      C (-40 : ℚ) * (A * X ^ 3) +
      C (8 : ℚ) * (A * X ^ 4) =
      C (4 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 0) +
      C (-8 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 1) +
      C (12 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 2) +
      C (-8 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 3) := by
    simp only [map_neg, map_ofNat, map_one, map_zero]
    linear_combination (1 : ℚ⟦X⟧) * hode
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have tp1 : coeff (k + 4) (C (4 : ℚ) * (d⁄dX ℚ A * X ^ 1)) =
      (4 : ℚ) * (coeff (k + 4) A * ((k : ℚ) + 4)) := by
    have e : k + 4 = k + 3 + 1 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 3 + 1 = k + 4 by omega]; push_cast; ring)
  have tp2 : coeff (k + 4) (C (-36 : ℚ) * (d⁄dX ℚ A * X ^ 2)) =
      (-36 : ℚ) * (coeff (k + 3) A * ((k : ℚ) + 3)) := by
    have e : k + 4 = k + 2 + 2 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 2 + 1 = k + 3 by omega]; push_cast; ring)
  have tp3 : coeff (k + 4) (C (80 : ℚ) * (d⁄dX ℚ A * X ^ 3)) =
      (80 : ℚ) * (coeff (k + 2) A * ((k : ℚ) + 2)) := by
    have e : k + 4 = k + 1 + 3 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 1 + 1 = k + 2 by omega]; push_cast; ring)
  have tp4 : coeff (k + 4) (C (-64 : ℚ) * (d⁄dX ℚ A * X ^ 4)) =
      (-64 : ℚ) * (coeff (k + 1) A * ((k : ℚ) + 1)) := by
    have e : k + 4 = k + 4 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (push_cast; ring)
  have tp5 : coeff (k + 4) (C (16 : ℚ) * (d⁄dX ℚ A * X ^ 5)) =
      (16 : ℚ) * (coeff k A * ((k : ℚ) + 0)) := by
    rcases k with _ | k'
    · simp [coeff_C_mul, coeff_mul_X_pow']
    · have e : k' + 1 + 4 = k' + 5 := by omega
      conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
      all_goals (push_cast; ring)
  have tq0 : coeff (k + 4) (C (4 : ℚ) * (A * X ^ 0)) = (4 : ℚ) * coeff (k + 4) A := by
    have e : k + 4 = k + 4 + 0 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq1 : coeff (k + 4) (C (-24 : ℚ) * (A * X ^ 1)) = (-24 : ℚ) * coeff (k + 3) A := by
    have e : k + 4 = k + 3 + 1 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq2 : coeff (k + 4) (C (48 : ℚ) * (A * X ^ 2)) = (48 : ℚ) * coeff (k + 2) A := by
    have e : k + 4 = k + 2 + 2 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq3 : coeff (k + 4) (C (-40 : ℚ) * (A * X ^ 3)) = (-40 : ℚ) * coeff (k + 1) A := by
    have e : k + 4 = k + 1 + 3 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq4 : coeff (k + 4) (C (8 : ℚ) * (A * X ^ 4)) = (8 : ℚ) * coeff (k) A := by
    have e : k + 4 = k + 4 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have th0 : coeff (k + 4) (C (4 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 0)) = 0 := by
    have e : k + 4 = k + 4 + 0 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have th1 : coeff (k + 4) (C (-8 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 1)) = 0 := by
    have e : k + 4 = k + 3 + 1 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have th2 : coeff (k + 4) (C (12 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 2)) = 0 := by
    have e : k + 4 = k + 2 + 2 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have th3 : coeff (k + 4) (C (-8 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 3)) = 0 := by
    have e : k + 4 = k + 1 + 3 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have hc := congrArg (coeff (k + 4)) key
  simp only [map_add, map_zero, tp1, tp2, tp3, tp4, tp5, tq0, tq1, tq2, tq3, tq4, th0, th1, th2, th3] at hc
  simp only [hcA] at hc
  rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  apply Int.cast_injective (α := ℚ)
  push_cast at hc ⊢
  linear_combination (1 / 4 : ℚ) * hc

end OMA.P215973

theorem OMA.solution : type_of% @OMA.S_oeis_a215973.main :=
  OMA.P215973.main' OMA.S_oeis_a215973.a (by rw [OMA.S_oeis_a215973.a])
    (fun n => by rw [OMA.S_oeis_a215973.a])
