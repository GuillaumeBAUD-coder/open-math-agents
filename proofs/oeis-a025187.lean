import OMAStatements.S_oeis_a025187
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# A025187: a polynomial certificate for Mathar's recurrence

Source: https://oeis.org/A025187
Credit: @CubeJerry
Canonical statement: @hermitokatt

The defining A025177 row is the coefficient sequence of
(1 + X^2) * (1 + X + X^2)^(m - 1). We prove this directly from the
canonical recursion, then verify an explicit polynomial differential
certificate and extract the required coefficient. The Euler operator
X*d/dX - k kills coefficient k. The certificate is checked by ring
normalization; it is not an assumption or an external computation.

A025184's OEIS history contains a 2018 suggestion by Mark van Hoeij to
use an algebraic diagonal generating function. Our displayed finite
certificate is independently derived and supplies the full recurrence.
-/

namespace A025Recurrence
open Polynomial

noncomputable def P : Polynomial ℤ := 1 + X + X ^ 2

noncomputable def B (n : ℕ) : Polynomial ℤ := (1 + X ^ 2) * P ^ (2 * n - 1)

theorem euler_coeff (f : Polynomial ℤ) (k : ℕ) :
    (X * derivative f - C (k : ℤ) * f).coeff k = 0 := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative, Nat.cast_add,
      Nat.cast_one]
    ring

theorem certificate_coeff (R Q : Polynomial ℤ) (m k : ℕ)
    (h : Q = X * P * derivative R +
      (C ((m + 1 : ℕ) : ℤ) * X * derivative P - C (k : ℤ) * P) * R) :
    (P ^ m * Q).coeff k = 0 := by
  have hid : P ^ m * Q =
      X * derivative (R * P ^ (m + 1)) - C (k : ℤ) * (R * P ^ (m + 1)) := by
    rw [h, derivative_mul, derivative_pow_succ, pow_succ]
    simp only [Nat.cast_add, Nat.cast_one, map_add, C_1, C_eq_natCast]
    ring
  rw [hid]
  exact euler_coeff _ _

theorem shift_coeff (f : Polynomial ℤ) (j k : ℕ) :
    (X ^ j * f).coeff (k + j) = f.coeff k := by
  simp [coeff_X_pow_mul]

end A025Recurrence

namespace A025Recurrence
open Polynomial

theorem mul_P_coeff (f : Polynomial ℤ) (k : ℕ) :
    (f * P).coeff k = f.coeff k +
      (if 1 ≤ k then f.coeff (k - 1) else 0) +
      (if 2 ≤ k then f.coeff (k - 2) else 0) := by
  have hX := coeff_mul_X_pow' f 1 k
  simp only [pow_one] at hX
  simp only [P, mul_add, mul_one, coeff_add, hX, coeff_mul_X_pow']

theorem row_coeff (T : ℕ → ℕ → ℤ)
    (h1 : ∀ k, T 1 k = if k = 0 ∨ k = 2 then 1 else 0)
    (hs : ∀ n k, T (n + 2) k = T (n + 1) k +
      (if 1 ≤ k then T (n + 1) (k - 1) else 0) +
      (if 2 ≤ k then T (n + 1) (k - 2) else 0))
    (n k : ℕ) : T (n + 1) k = ((1 + X ^ 2) * P ^ n).coeff k := by
  induction n generalizing k with
  | zero =>
      rw [h1]
      by_cases h0 : k = 0
      · subst k
        simp
      · by_cases h2 : k = 2
        · subst k
          simp [coeff_one]
        · simp [h0, h2, coeff_one, coeff_X_pow]
  | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by omega, hs, ih, ih, ih]
      rw [pow_succ P n, ← mul_assoc, mul_P_coeff]

theorem even_row_coeff (T : ℕ → ℕ → ℤ)
    (h1 : ∀ k, T 1 k = if k = 0 ∨ k = 2 then 1 else 0)
    (hs : ∀ n k, T (n + 2) k = T (n + 1) k +
      (if 1 ≤ k then T (n + 1) (k - 1) else 0) +
      (if 2 ≤ k then T (n + 1) (k - 2) else 0))
    (n k : ℕ) (hn : 1 ≤ n) : T (2 * n) k = (B n).coeff k := by
  have h := row_coeff T h1 hs (2 * n - 1) k
  simpa only [show 2 * n - 1 + 1 = 2 * n by omega, B] using h

end A025Recurrence

namespace A025187Proof

theorem a_eq (n : ℕ) (hn : 1 ≤ n) :
    OMA.S_oeis_a025187.a n = (A025Recurrence.B n).coeff (n - 1) := by
  exact A025Recurrence.even_row_coeff OMA.S_oeis_a025187.T
    (fun _ => rfl) (fun _ _ => rfl) n (n - 1) hn

end A025187Proof

namespace A025Recurrence
open Polynomial

noncomputable def R187 (n : ℤ) : Polynomial ℤ :=
  C (-12 * n * (n - 2) * (3 * n - 1) * (3 * n + 1) * (1573 * n - 2085)) * X ^ 0 +
  C (-1448707 * n ^ 5 + 10255188 * n ^ 4 - 28736416 * n ^ 3 + 39924510 * n ^ 2 - 26911261 * n + 6720078) * X ^ 1 +
  C (85345 * n ^ 5 - 2472891 * n ^ 4 + 14498437 * n ^ 3 - 34089645 * n ^ 2 + 36576370 * n - 15089136) * X ^ 2 +
  C (3091595 * n ^ 5 - 26830934 * n ^ 4 + 98092230 * n ^ 3 - 181404832 * n ^ 2 + 166265839 * n - 60000330) * X ^ 3 +
  C (2 * (3288519 * n ^ 5 - 25733824 * n ^ 4 + 86966990 * n ^ 3 - 153942374 * n ^ 2 + 138017059 * n - 49063314)) * X ^ 4 +
  C (2 * (5892614 * n ^ 5 - 44912635 * n ^ 4 + 145075939 * n ^ 3 - 244143113 * n ^ 2 + 208523799 * n - 70829820)) * X ^ 5 +
  C (2 * (n - 2) * (5622721 * n ^ 4 - 28039847 * n ^ 3 + 62062580 * n ^ 2 - 66558079 * n + 27158385)) * X ^ 6 +
  C ((n - 2) * (9902763 * n ^ 4 - 46410566 * n ^ 3 + 95428320 * n ^ 2 - 96434938 * n + 37711029)) * X ^ 7 +
  C ((n - 2) * (6024733 * n ^ 4 - 23572197 * n ^ 3 + 40521695 * n ^ 2 - 36782235 * n + 13857156)) * X ^ 8 +
  C ((n - 2) * (n - 1) * (2978729 * n ^ 3 - 7131221 * n ^ 2 + 6884855 * n - 3535179)) * X ^ 9 +
  C (8 * (n - 2) * (n - 1) * (1573 * n - 2085) * (92 * n ^ 2 - 37 * n + 3)) * X ^ 10 +
  C (4 * (n - 2) * (n - 1) * (3 * n - 1) * (17 * n - 1) * (1573 * n - 2085)) * X ^ 11 +
  C (12 * n * (n - 2) * (n - 1) * (3 * n - 1) * (1573 * n - 2085)) * X ^ 12

noncomputable def Q187 (n : ℤ) : Polynomial ℤ :=
  (1 + X ^ 2) * (
    C (12 * n * (3 * n - 1) * (3 * n + 1) * (1573 * n - 2085)) * X ^ 0 * P ^ 6 +
    C (259519 * n ^ 4 - 6550685 * n ^ 3 + 19840883 * n ^ 2 - 20466403 * n + 6720078) * X ^ 1 * P ^ 4 +
    C (-54 * (2 * n - 3) * (63141 * n ^ 3 - 343882 * n ^ 2 + 645379 * n - 388606)) * X ^ 2 * P ^ 2 +
    C (-324 * (n - 3) * (2 * n - 5) * (2 * n - 3) * (4693 * n - 5417)) * X ^ 3 * P ^ 0)

set_option maxHeartbeats 4000000 in
theorem certificate187 (n : ℤ) :
    C ((n - 1) * (n - 2)) * Q187 n =
      X * P * derivative (R187 n) +
        (C (2 * n - 6) * X * derivative P - C (n - 1) * P) * R187 n := by
  simp only [R187, Q187, P, derivative_add, derivative_mul, derivative_C,
    derivative_X_pow, derivative_X, derivative_one]
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, C_0, C_1, zero_mul, mul_zero,
    zero_add, add_zero, pow_zero, pow_one, one_mul, mul_one]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, C_ofNat, C_1]
  ring

end A025Recurrence

namespace A025Recurrence
open Polynomial

theorem recurrence187 (m : ℕ) :
    12 * ((m : ℤ) + 4) * (1573 * ((m : ℤ) + 4) - 2085) * (3 * ((m : ℤ) + 4) - 1) * (3 * ((m : ℤ) + 4) + 1) * (B (m + 4)).coeff (m + 3)
      + (259519 * ((m : ℤ) + 4) ^ 4 - 6550685 * ((m : ℤ) + 4) ^ 3 + 19840883 * ((m : ℤ) + 4) ^ 2 - 20466403 * ((m : ℤ) + 4) + 6720078) * (B (m + 3)).coeff (m + 2)
      - 54 * (2 * ((m : ℤ) + 4) - 3) * (63141 * ((m : ℤ) + 4) ^ 3 - 343882 * ((m : ℤ) + 4) ^ 2 + 645379 * ((m : ℤ) + 4) - 388606) * (B (m + 2)).coeff (m + 1)
      - 324 * (((m : ℤ) + 4) - 3) * (4693 * ((m : ℤ) + 4) - 5417) * (2 * ((m : ℤ) + 4) - 3) * (2 * ((m : ℤ) + 4) - 5) * (B (m + 1)).coeff m = 0 := by
  have hc : (P ^ (2 * m + 1) * Q187 ((m : ℤ) + 4)).coeff (m + 3) = 0 := by
    have h : (P ^ (2 * m + 1) * (C ((((m : ℤ) + 4) - 1) * (((m : ℤ) + 4) - 2)) * Q187 ((m : ℤ) + 4))).coeff (m + 3) = 0 := by
      apply certificate_coeff (R187 ((m : ℤ) + 4))
      have h1 : (((2 * m + 1) + 1 : ℕ) : ℤ) = 2 * ((m : ℤ) + 4) - 6 := by omega
      have h2 : ((m + 3 : ℕ) : ℤ) = ((m : ℤ) + 4) - 1 := by omega
      rw [h1, h2]
      exact certificate187 _
    rw [show P ^ (2 * m + 1) * (C ((((m : ℤ) + 4) - 1) * (((m : ℤ) + 4) - 2)) * Q187 ((m : ℤ) + 4)) =
      C ((((m : ℤ) + 4) - 1) * (((m : ℤ) + 4) - 2)) * (P ^ (2 * m + 1) * Q187 ((m : ℤ) + 4)) by ring, coeff_C_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by omega) (by omega))
  have he (j : ℕ) : B (m + j + 1) = (1 + X ^ 2) * (P ^ (2 * m + 1) * P ^ (2 * j)) := by
    unfold B
    rw [show 2 * (m + j + 1) - 1 = (2 * m + 1) + 2 * j by omega, pow_add]
  have hp : P ^ (2 * m + 1) * Q187 ((m : ℤ) + 4) =
      C (12 * ((m : ℤ) + 4) * (3 * ((m : ℤ) + 4) - 1) * (3 * ((m : ℤ) + 4) + 1) * (1573 * ((m : ℤ) + 4) - 2085)) * B (m + 4) +
      C (259519 * ((m : ℤ) + 4) ^ 4 - 6550685 * ((m : ℤ) + 4) ^ 3 + 19840883 * ((m : ℤ) + 4) ^ 2 - 20466403 * ((m : ℤ) + 4) + 6720078) * (X ^ 1 * B (m + 3)) +
      C (-54 * (2 * ((m : ℤ) + 4) - 3) * (63141 * ((m : ℤ) + 4) ^ 3 - 343882 * ((m : ℤ) + 4) ^ 2 + 645379 * ((m : ℤ) + 4) - 388606)) * (X ^ 2 * B (m + 2)) +
      C (-324 * (((m : ℤ) + 4) - 3) * (2 * ((m : ℤ) + 4) - 5) * (2 * ((m : ℤ) + 4) - 3) * (4693 * ((m : ℤ) + 4) - 5417)) * (X ^ 3 * B (m + 1)) := by
    have h1 := he 0
    have h2 := he 1
    have h3 := he 2
    have h4 := he 3
    norm_num only [Nat.reduceMul, Nat.add_zero, Nat.reduceAdd, Nat.add_assoc] at h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    unfold Q187
    ring
  rw [hp] at hc
  simp only [coeff_add, coeff_C_mul] at hc
  have hs1 := shift_coeff (B (m + 3)) 1 (m + 2)
  have hs2 := shift_coeff (B (m + 2)) 2 (m + 1)
  have hs3 := shift_coeff (B (m + 1)) 3 m
  norm_num only [Nat.add_assoc, Nat.reduceAdd] at hs1 hs2 hs3
  rw [hs1, hs2, hs3] at hc
  linear_combination hc

end A025Recurrence

theorem OMA.solution : type_of% @OMA.S_oeis_a025187.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega,
    show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega]
  rw [A025187Proof.a_eq (m + 4) (by omega),
    A025187Proof.a_eq (m + 3) (by omega),
    A025187Proof.a_eq (m + 2) (by omega),
    A025187Proof.a_eq (m + 1) (by omega)]
  simpa only [Nat.cast_add, Nat.cast_ofNat,
    show m + 4 - 1 = m + 3 by omega,
    show m + 3 - 1 = m + 2 by omega,
    show m + 2 - 1 = m + 1 by omega,
    show m + 1 - 1 = m by omega] using A025Recurrence.recurrence187 m
