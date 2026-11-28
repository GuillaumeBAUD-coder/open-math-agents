import OMAStatements.S_oeis_a386829
import Mathlib

/-!
# A386829: the D-finite recurrence

Write p = 3X + 2X^2 and let L be the linear functional on rational polynomials with
L(X^m) = 1/(m+1). Expanding p^n = X^n (3 + 2X)^n shows a(n) = c(n) * L(p^n) with
c(n) = (2n+1)!/(n!)^2. Since L(f') = f(1) - f(0) and (p' p^n)' = (8n+4) p^n + 9n p^(n-1)
(because p'^2 = 9 + 8p), one gets (8n+4) L(p^n) + 9n L(p^(n-1)) = 7 * 5^n for n >= 1.
Eliminating 5^n between two consecutive instances gives the recurrence.
-/

open Polynomial

namespace OMA.Helpers

noncomputable def a386829L : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun m => ((m : ℚ) + 1)⁻¹ • LinearMap.id)

lemma a386829L_monomial (m : ℕ) (c : ℚ) :
    a386829L (monomial m c) = ((m : ℚ) + 1)⁻¹ * c := by
  unfold a386829L
  rw [Polynomial.lsum_apply, sum_monomial_index]
  · simp
  · simp

lemma a386829L_derivative (f : ℚ[X]) :
    a386829L (derivative f) = f.eval 1 - f.eval 0 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, eval_add, hp, hq]; ring
  | monomial n c =>
    rw [derivative_monomial, a386829L_monomial]
    rcases n with _ | k
    · simp
    · simp only [Nat.add_sub_cancel, eval_monomial, one_pow, mul_one,
        zero_pow (Nat.succ_ne_zero k), mul_zero, sub_zero, Nat.cast_succ]
      field_simp

lemma a386829_deriv (m : ℕ) :
    derivative ((3 + 4 * X) * (3 * X + 2 * X ^ 2) ^ (m + 1) : ℚ[X]) =
      C (8 * ((m : ℚ) + 1) + 4) * (3 * X + 2 * X ^ 2) ^ (m + 1) +
        C (9 * ((m : ℚ) + 1)) * (3 * X + 2 * X ^ 2) ^ m := by
  rw [derivative_mul, derivative_pow]
  simp only [derivative_mul, derivative_X, derivative_X_pow, derivative_ofNat,
    map_add, map_mul, map_natCast, map_ofNat, map_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  ring

noncomputable def a386829I (n : ℕ) : ℚ := a386829L ((3 * X + 2 * X ^ 2 : ℚ[X]) ^ n)

lemma a386829_E (m : ℕ) :
    (8 * ((m : ℚ) + 1) + 4) * a386829I (m + 1) + 9 * ((m : ℚ) + 1) * a386829I m
      = 7 * 5 ^ (m + 1) := by
  have h := a386829L_derivative ((3 + 4 * X) * (3 * X + 2 * X ^ 2) ^ (m + 1) : ℚ[X])
  rw [a386829_deriv, map_add, ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul, map_smul] at h
  simp only [smul_eq_mul] at h
  unfold a386829I
  rw [h]
  simp
  norm_num


lemma a386829_term (n k : ℕ) :
    (X : ℚ[X]) ^ n * ((3 : ℚ[X]) ^ k * (2 * X) ^ (n - k) * ((n.choose k : ℕ) : ℚ[X])) =
      monomial (n + (n - k)) ((3 : ℚ) ^ k * 2 ^ (n - k) * (n.choose k : ℚ)) := by
  rw [← C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_pow, map_ofNat, map_natCast, mul_pow, pow_add]
  ring

lemma a386829I_eq (n : ℕ) :
    a386829I n = ∑ k ∈ Finset.range (n + 1),
      (((n + (n - k) : ℕ) : ℚ) + 1)⁻¹ * ((3 : ℚ) ^ k * 2 ^ (n - k) * (n.choose k : ℚ)) := by
  unfold a386829I
  have hp : (3 * X + 2 * X ^ 2 : ℚ[X]) = X * (3 + 2 * X) := by ring
  rw [hp, mul_pow, add_pow, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [a386829_term, a386829L_monomial]

noncomputable def a386829c (n : ℕ) : ℚ := ((2 * n + 1).factorial : ℚ) / ((n.factorial : ℚ) * n.factorial)

lemma a386829_choose (n k : ℕ) (hk : k ≤ n) :
    ((2 * n + 1).choose k : ℚ) * ((2 * n - k).choose (n - k) : ℚ) =
      a386829c n * ((((n + (n - k) : ℕ) : ℚ) + 1)⁻¹ * (n.choose k : ℚ)) := by
  unfold a386829c
  rw [Nat.cast_choose ℚ (by omega : k ≤ 2 * n + 1), Nat.cast_choose ℚ (by omega : n - k ≤ 2 * n - k),
    Nat.cast_choose ℚ hk]
  have h1 : 2 * n + 1 - k = (n + (n - k)) + 1 := by omega
  have h2 : 2 * n - k - (n - k) = n := by omega
  have h3 : 2 * n - k = n + (n - k) := by omega
  rw [h1, h2, h3, Nat.factorial_succ]
  push_cast
  field_simp
  rw [Nat.factorial_succ]
  push_cast
  ring

lemma a386829_a (n : ℕ) : ((OMA.S_oeis_a386829.a n : ℤ) : ℚ) = a386829c n * a386829I n := by
  rw [a386829I_eq, Finset.mul_sum]
  unfold OMA.S_oeis_a386829.a
  push_cast
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ n := by simp at hk; omega
  rw [mul_assoc, a386829_choose n k hk']
  push_cast
  ring

lemma a386829_c (j : ℕ) : ((j : ℚ) + 1) * a386829c (j + 1) = 2 * (2 * (j : ℚ) + 3) * a386829c j := by
  unfold a386829c
  rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ j]
  push_cast
  field_simp
  ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a386829.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [OMA.Helpers.a386829_a, OMA.Helpers.a386829_a, OMA.Helpers.a386829_a]
  have hc1 := OMA.Helpers.a386829_c (m + 1)
  have hc0 := OMA.Helpers.a386829_c m
  have hE1 := OMA.Helpers.a386829_E (m + 1)
  have hE0 := OMA.Helpers.a386829_E m
  push_cast at hc1 hE1
  linear_combination 2 * OMA.Helpers.a386829I (m + 2) * hc1 + 45 * OMA.Helpers.a386829I m * hc0
    + OMA.Helpers.a386829c (m + 1) * (hE1 - 5 * hE0)
