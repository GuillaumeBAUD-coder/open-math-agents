import OMAStatements.S_oeis_a185010
import Mathlib

open OMA.S_oeis_a185010 in
theorem OMA.solution : type_of% @OMA.S_oeis_a185010.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have c (k : ℕ) : ((k : ℤ) + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
    have c := Nat.succ_mul_centralBinom_succ k
    rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at c
    have c := congrArg (Nat.cast (R := ℤ)) c
    push_cast at c
    apply mul_left_cancel₀ (show (k : ℤ) + 1 ≠ 0 by positivity)
    linear_combination c
  have c1 := c (k + 1)
  have hb : (b (k + 3) : ℤ) = 2 * b (k + 2) + 3 * b (k + 1) := by norm_cast
  simp only [a, show k + 2 - 1 = k + 1 by omega, Nat.add_sub_cancel] at *
  push_cast at *
  linear_combination ((k : ℤ) + 2) * b (k + 3) * c1 + 2 * ((k : ℤ) + 2) * (2 * k + 3) * catalan (k + 1) * hb +
    6 * (2 * (k : ℤ) + 3) * b (k + 1) * c k
