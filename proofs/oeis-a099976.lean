import OMAStatements.S_oeis_a099976
import Mathlib

open OMA.S_oeis_a099976 in
theorem OMA.solution : type_of% @OMA.S_oeis_a099976.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have ea : a (k + 1) = Nat.centralBinom (2 * k + 2 + 1) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    simp only [a]
    congr 1 <;> ring
  have eb : a (k + 1 - 1) = Nat.centralBinom (2 * k + 1) := by
    rw [show k + 1 - 1 = k by omega, Nat.centralBinom_eq_two_mul_choose]
    simp only [a]
    congr 1 <;> ring
  have h1 : (2 * k + 2 + 1) * Nat.centralBinom (2 * k + 2 + 1)
      = 2 * (2 * (2 * k + 2) + 1) * Nat.centralBinom (2 * k + 2) :=
    Nat.succ_mul_centralBinom_succ (2 * k + 2)
  have h2 : (2 * k + 2) * Nat.centralBinom (2 * k + 2)
      = 2 * (2 * (2 * k + 1) + 1) * Nat.centralBinom (2 * k + 1) := by
    have h := Nat.succ_mul_centralBinom_succ (2 * k + 1)
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring] at h
    exact h
  have h1' := congrArg (Nat.cast : ℕ → ℤ) h1
  have h2' := congrArg (Nat.cast : ℕ → ℤ) h2
  push_cast at h1' h2'
  rw [ea, eb]
  push_cast
  linear_combination ((k : ℤ) + 1) * h1' + (4 * (k : ℤ) + 5) * h2'
