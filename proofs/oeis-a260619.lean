import OMAStatements.S_oeis_a260619
import Mathlib.Tactic.Ring

namespace OMA.P_oeis_a260619

open OMA.S_oeis_a260619

private lemma arithmeticDerivative_one : arithmeticDerivative 1 = 0 := by
  simp [arithmeticDerivative]

private lemma arithmeticDerivative_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    arithmeticDerivative (a * b) = arithmeticDerivative a * b + a * arithmeticDerivative b := by
  unfold arithmeticDerivative
  have hsub_a : a.primeFactors ⊆ (a * b).primeFactors := by
    rw [Nat.primeFactors_mul ha hb]
    exact Finset.subset_union_left
  have hsub_b : b.primeFactors ⊆ (a * b).primeFactors := by
    rw [Nat.primeFactors_mul ha hb]
    exact Finset.subset_union_right
  have hsplit :
      ∑ p ∈ (a * b).primeFactors, (a * b).factorization p * (a * b / p) =
      ∑ p ∈ (a * b).primeFactors,
        (a.factorization p * (a * b / p) + b.factorization p * (a * b / p)) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.factorization_mul ha hb, Finsupp.add_apply, add_mul]
  rw [hsplit, Finset.sum_add_distrib]
  have hleft :
      ∑ p ∈ (a * b).primeFactors, a.factorization p * (a * b / p) =
      (∑ p ∈ a.primeFactors, a.factorization p * (a / p)) * b := by
    rw [Finset.sum_mul]
    symm
    refine Finset.sum_subset_zero_on_sdiff hsub_a ?_ ?_
    · intro p hp
      rw [Finset.mem_sdiff] at hp
      have h0 : a.factorization p = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        by_contra h
        push Not at h
        exact hp.2 (Nat.mem_primeFactors.mpr ⟨h.1, h.2.1, h.2.2⟩)
      simp [h0]
    · intro p hp
      have hdvd : p ∣ a := (Nat.mem_primeFactors.mp hp).2.1
      rw [mul_assoc, Nat.div_mul_right_comm hdvd]
  have hright :
      ∑ p ∈ (a * b).primeFactors, b.factorization p * (a * b / p) =
      a * ∑ p ∈ b.primeFactors, b.factorization p * (b / p) := by
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_subset_zero_on_sdiff hsub_b ?_ ?_
    · intro p hp
      rw [Finset.mem_sdiff] at hp
      have h0 : b.factorization p = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        by_contra h
        push Not at h
        exact hp.2 (Nat.mem_primeFactors.mpr ⟨h.1, h.2.1, h.2.2⟩)
      simp [h0]
    · intro p hp
      have hdvd : p ∣ b := (Nat.mem_primeFactors.mp hp).2.1
      rw [Nat.mul_div_assoc a hdvd]
      ring
  rw [hleft, hright]

private lemma arithmeticDerivative_pow {a : ℕ} (ha : a ≠ 0) :
    ∀ k : ℕ, arithmeticDerivative (a ^ k) = k * a ^ (k - 1) * arithmeticDerivative a
  | 0 => by simp [arithmeticDerivative_one]
  | k + 1 => by
    rw [pow_succ, arithmeticDerivative_mul (pow_ne_zero k ha) ha, arithmeticDerivative_pow ha k]
    cases k with
    | zero => simp [arithmeticDerivative_one]
    | succ m =>
      simp only [Nat.add_sub_cancel]
      rw [pow_succ a m]
      ring

private lemma arithmeticDerivative_self_pow {k : ℕ} (hk : k ≠ 0) :
    arithmeticDerivative (k ^ k) = k ^ k * arithmeticDerivative k := by
  rw [arithmeticDerivative_pow hk k]
  have hpow : k * k ^ (k - 1) = k ^ k := by
    cases k with
    | zero => exact (hk rfl).elim
    | succ m => rw [Nat.add_sub_cancel, pow_succ']
  rw [hpow]

private lemma hyperfactorial_ne_zero : ∀ n : ℕ, hyperfactorial n ≠ 0
  | 0 => by simp [hyperfactorial]
  | n + 1 => by
    rw [hyperfactorial]
    exact mul_ne_zero (hyperfactorial_ne_zero n) (pow_ne_zero _ (Nat.succ_ne_zero n))

theorem main_proof : type_of% @OMA.S_oeis_a260619.main := by
  intro n
  induction n with
  | zero =>
    simp [hyperfactorial, derivativeSum, arithmeticDerivative_one]
  | succ n ih =>
    rw [hyperfactorial, derivativeSum, Finset.sum_range_succ, ← derivativeSum]
    rw [arithmeticDerivative_mul (hyperfactorial_ne_zero n) (pow_ne_zero _ (Nat.succ_ne_zero n))]
    rw [ih, arithmeticDerivative_self_pow (Nat.succ_ne_zero n)]
    change hyperfactorial n * derivativeSum n * (n + 1) ^ (n + 1) +
        hyperfactorial n * ((n + 1) ^ (n + 1) * arithmeticDerivative (n + 1)) =
      hyperfactorial n * (n + 1) ^ (n + 1) * (derivativeSum n + arithmeticDerivative (n + 1))
    ring

end OMA.P_oeis_a260619

theorem OMA.solution : type_of% @OMA.S_oeis_a260619.main :=
  OMA.P_oeis_a260619.main_proof
