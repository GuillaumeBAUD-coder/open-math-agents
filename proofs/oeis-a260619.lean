import OMAStatements.S_oeis_a260619
import Mathlib

namespace OMA.A260619Proof

open OMA.S_oeis_a260619

lemma D_eq (n : ℕ) (S : Finset ℕ) (h : n.primeFactors ⊆ S) :
    arithmeticDerivative n = ∑ p ∈ S, n.factorization p * (n / p) := by
  unfold arithmeticDerivative
  apply Finset.sum_subset h
  intro p _ hp
  have : n.factorization p = 0 := by
    rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
    exact hp
  simp [this]

lemma term_left (a b p : ℕ) :
    a.factorization p * (a * b / p) = b * (a.factorization p * (a / p)) := by
  by_cases h : a.factorization p = 0
  · simp [h]
  · have hd : p ∣ a := Nat.dvd_of_factorization_pos h
    rw [← Nat.div_mul_right_comm hd]
    ring

lemma term_right (a b p : ℕ) :
    b.factorization p * (a * b / p) = a * (b.factorization p * (b / p)) := by
  by_cases h : b.factorization p = 0
  · simp [h]
  · have hd : p ∣ b := Nat.dvd_of_factorization_pos h
    rw [Nat.mul_div_assoc a hd]
    ring

lemma leibniz (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    arithmeticDerivative (a * b) = a * arithmeticDerivative b + b * arithmeticDerivative a := by
  have hS : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors :=
    Nat.primeFactors_mul ha hb
  rw [D_eq (a * b) (a.primeFactors ∪ b.primeFactors) hS.le,
    D_eq a (a.primeFactors ∪ b.primeFactors) Finset.subset_union_left,
    D_eq b (a.primeFactors ∪ b.primeFactors) Finset.subset_union_right,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply, add_mul, term_left, term_right]
  ring

lemma power (k : ℕ) (hk : k ≠ 0) (m : ℕ) :
    arithmeticDerivative (k ^ (m + 1)) = (m + 1) * k ^ m * arithmeticDerivative k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ k (m + 1), leibniz _ _ (pow_ne_zero _ hk) hk, ih]
    ring

lemma hyper_ne_zero (n : ℕ) : hyperfactorial n ≠ 0 := by
  induction n with
  | zero => simp [hyperfactorial]
  | succ n ih =>
    simp only [hyperfactorial]
    exact mul_ne_zero ih (pow_ne_zero _ (Nat.succ_ne_zero n))

end OMA.A260619Proof

open OMA.S_oeis_a260619 OMA.A260619Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a260619.main := by
  intro n
  induction n with
  | zero =>
    simp [hyperfactorial, derivativeSum, arithmeticDerivative]
  | succ n ih =>
    simp only [hyperfactorial]
    rw [leibniz _ _ (hyper_ne_zero n) (pow_ne_zero _ (Nat.succ_ne_zero n)), ih,
      power (n + 1) (Nat.succ_ne_zero n) n]
    simp only [derivativeSum, Finset.sum_range_succ, Nat.succ_eq_add_one]
    ring
