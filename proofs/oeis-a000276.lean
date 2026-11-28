import OMAStatements.S_oeis_a000276
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a000276.main := by
  constructor <;> intro n hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [OMA.S_oeis_a000276.a, Nat.reduceSubDiff, Nat.factorial_succ, harmonic_succ]
    push_cast
    field_simp
    ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    simp only [OMA.S_oeis_a000276.a, Nat.reduceSubDiff, Nat.factorial_succ, harmonic_succ]
    push_cast
    field_simp
    ring
