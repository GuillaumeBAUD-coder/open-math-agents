import OMAStatements.S_oeis_a000276
import Mathlib

open OMA.S_oeis_a000276 in
theorem OMA.solution : type_of% @OMA.S_oeis_a000276.main := by
  have k (m j : ℕ) : a (m + 4 + j) = ((m + 3 + j).factorial : ℚ) * (harmonic (m + 2 + j) - 1) := by
    simp [a, show m + 4 + j - 1 = m + 3 + j by omega, show m + 4 + j - 2 = m + 2 + j by omega]
  constructor <;> rintro n hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 + 2 := ⟨n - 6, by omega⟩
    rw [show m + 4 + 2 - 1 = m + 4 + 1 by omega, show m + 4 + 2 - 2 = m + 4 + 0 by omega, k, k, k]
    simp only [Nat.factorial_succ, harmonic_succ, add_zero]
    push_cast
    field_simp
    ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 + 3 := ⟨n - 7, by omega⟩
    rw [show m + 4 + 3 - 1 = m + 4 + 2 by omega, show m + 4 + 3 - 2 = m + 4 + 1 by omega,
      show m + 4 + 3 - 3 = m + 4 + 0 by omega, k, k, k, k]
    simp only [Nat.factorial_succ, harmonic_succ, add_zero]
    push_cast
    field_simp
    ring
