import OMAStatements.S_oeis_a260619
import Mathlib.Tactic
open Finset OMA.S_oeis_a260619

lemma L {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    arithmeticDerivative (a * b) = b * arithmeticDerivative a + a * arithmeticDerivative b := by
  have k (x y p : ℕ) : x.factorization p * (x * y / p) = y * (x.factorization p * (x / p)) := by
    by_cases h : p ∣ x
    · rw [Nat.mul_comm x, Nat.mul_div_assoc _ h]; ring
    · simp [Nat.factorization_eq_zero_of_not_dvd h]
  unfold arithmeticDerivative
  rw [Nat.primeFactors_mul ha hb, mul_sum, mul_sum, sum_subset (subset_union_left (s₁ := a.primeFactors) (s₂ := b.primeFactors)),
    sum_subset (subset_union_right (s₁ := a.primeFactors) (s₂ := b.primeFactors)), ← sum_add_distrib]
  · refine sum_congr rfl fun p _ => ?_
    rw [Nat.factorization_mul ha hb, Finsupp.add_apply, add_mul, k, Nat.mul_comm a, k]
  all_goals intros; simp_all [Nat.factorization_eq_zero_iff]

lemma P {m : ℕ} (h : m ≠ 0) (k : ℕ) :
    arithmeticDerivative (m ^ (k + 1)) = (k + 1) * m ^ k * arithmeticDerivative m := by
  induction k <;> simp_all [pow_succ m, L]; ring

theorem OMA.solution : type_of% @OMA.S_oeis_a260619.main := by
  intro n
  have H : ∀ n, hyperfactorial n ≠ 0 := by intro n; induction n <;> simp_all [hyperfactorial]
  induction n with
  | zero => simp [hyperfactorial, derivativeSum, arithmeticDerivative]
  | succ n ih =>
    simp only [hyperfactorial, derivativeSum, sum_range_succ] at *
    rw [L (H n) (by positivity), P (by omega : n + 1 ≠ 0), ih]
    ring
