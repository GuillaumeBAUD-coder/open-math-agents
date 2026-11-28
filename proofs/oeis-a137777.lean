import OMAStatements.S_oeis_a137777
import Mathlib

/-
A137777: the row sums of 2 (n+2)! times the coefficients of the Bernoulli polynomial B_(n+1)(x)
equal 2 * target(n+2).

The sum of all coefficients of B_(n+1) is its value at 1, which is the Bernoulli number with the
convention B_1 = 1/2 (bernoulli_eval_one); the polynomial has degree at most n + 1, so the range
of the sum covers every coefficient. For n = 0 this gives 2 * 2 * 1/2 = 2. For n >= 1 the index
n + 1 is not 1, where the two conventions for Bernoulli numbers agree.
-/

namespace OMA.P137777

open Finset

lemma coeff_sum (n : ℕ) :
    ∑ k ∈ range (n + 2), (Polynomial.bernoulli (n + 1)).coeff k = bernoulli' (n + 1) := by
  have hdeg : (Polynomial.bernoulli (n + 1)).natDegree < n + 2 := by
    have : (Polynomial.bernoulli (n + 1)).natDegree ≤ n + 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [Polynomial.coeff_bernoulli]
      simp [Nat.choose_eq_zero_of_lt hN]
    omega
  rw [← Polynomial.bernoulli_eval_one, Polynomial.eval_eq_sum_range' hdeg]
  simp

lemma main' (derivativeEntry : ℕ → ℕ → ℚ)
    (hd : ∀ n k, derivativeEntry n k =
      2 * ((n + 2).factorial : ℚ) * (Polynomial.bernoulli (n + 1)).coeff k)
    (targetSequence : ℕ → ℚ)
    (ht : ∀ m, targetSequence m =
      if m = 0 then 0 else if m ≤ 2 then 1 else (m.factorial : ℚ) * bernoulli (m - 1)) :
    ∀ n : ℕ, ∑ k ∈ range (n + 2), derivativeEntry n k = 2 * targetSequence (n + 2) := by
  intro n
  simp only [hd, ← Finset.mul_sum, coeff_sum, ht]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [bernoulli'_one]
  · rw [if_neg (by omega), if_neg (by omega), show n + 2 - 1 = n + 1 by omega,
      bernoulli_eq_bernoulli'_of_ne_one (by omega : n + 1 ≠ 1)]
    ring

end OMA.P137777

theorem OMA.solution : type_of% @OMA.S_oeis_a137777.main :=
  OMA.P137777.main' OMA.S_oeis_a137777.derivativeEntry (fun _ _ => rfl)
    OMA.S_oeis_a137777.targetSequence (fun _ => rfl)
