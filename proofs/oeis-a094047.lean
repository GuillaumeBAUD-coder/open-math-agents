import OMAStatements.S_oeis_a094047
import Mathlib

open OMA.S_oeis_a094047

theorem OMA.solution : type_of% @OMA.S_oeis_a094047.main := by
  intro a _ _ _ h n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have h0 := h (k + 6) (by omega)
  have h1 := h (k + 5) (by omega)
  have h2 := h (k + 4) (by omega)
  simp only [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
    show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega,
    show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega, show k + 4 - 1 = k + 3 by omega,
    show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega] at h0 h1 h2 ⊢
  rw [Nat.factorial_succ (k + 2), Nat.factorial_succ (k + 1)] at h0
  rw [Nat.factorial_succ (k + 1)] at h1
  rw [pow_succ, pow_succ] at h0
  rw [pow_succ] at h1
  push_cast at h0 h1 h2 ⊢
  linear_combination h0 + ((k : ℚ) + 3) * h1 + (-(k : ℚ) - 2) * h2
