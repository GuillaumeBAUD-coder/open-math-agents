import OMAStatements.S_oeis_a152929
import Mathlib

open OMA.S_oeis_a152929

theorem OMA.solution : type_of% @OMA.S_oeis_a152929.main := by
  have key : ∀ n : ℕ, 2 * a (n + 1) = 163 * (Nat.fib (n + 1) : ℤ) + 63 * lucas (n + 1) ∧
      2 * a (n + 2) = 163 * (Nat.fib (n + 2) : ℤ) + 63 * lucas (n + 2) := by
    intro n
    induction n with
    | zero => refine ⟨?_, ?_⟩ <;> simp [a, lucas, Nat.fib_add_two]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h3 : a (k + 3) = a (k + 2) + a (k + 1) := rfl
      have l3 : lucas (k + 3) = lucas (k + 2) + lucas (k + 1) := rfl
      have f3 : (Nat.fib (k + 3) : ℤ) = Nat.fib (k + 2) + Nat.fib (k + 1) := by
        rw [Nat.fib_add_two]; push_cast; ring
      rw [show k + 1 + 2 = k + 3 by ring, h3, l3, f3]
      linear_combination ih.1 + ih.2
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (key m).1
