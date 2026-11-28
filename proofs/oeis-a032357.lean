import OMAStatements.S_oeis_a032357
import Mathlib

open OMA.S_oeis_a032357 in
theorem OMA.solution : type_of% @OMA.S_oeis_a032357.main := by
  have st (n : ℕ) : a (n + 1) = catalan (n + 1) - a n := by
    rw [a, Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul, a, sub_eq_add_neg,
      ← Finset.sum_neg_distrib, add_comm]
    exact congrArg _ (Finset.sum_congr rfl fun k hk => by
      rw [show n + 1 - k = n - k + 1 by simp at hk; omega, pow_succ]; ring)
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have c := Nat.succ_mul_centralBinom_succ (m + 1)
  rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at c
  have c := congrArg (Nat.cast (R := ℤ)) c
  simp only [show m + 2 - 1 = m + 1 by omega, Nat.add_sub_cancel, st]
  push_cast at c ⊢
  apply mul_left_cancel₀ (show (m : ℤ) + 2 ≠ 0 by positivity)
  linear_combination c
