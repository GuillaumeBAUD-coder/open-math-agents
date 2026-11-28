import OMAStatements.S_oeis_a000276
import Mathlib
open OMA.S_oeis_a000276
lemma OMA.a276key (m : ℕ) : a (m+4) = ((m+3).factorial : ℚ) * (harmonic (m+2) - 1) := by
  simp [a]
lemma OMA.a276key5 (m : ℕ) : a (m+5) = ((m+3).factorial : ℚ) * (m+4) * (harmonic (m+2) + 1/(m+3) - 1) := by
  have h1 : a (m+5) = a ((m+1)+4) := rfl
  rw [h1, OMA.a276key, show m+1+3 = (m+3)+1 by omega, Nat.factorial_succ, show m+1+2 = (m+2)+1 by omega,
    harmonic_succ]
  push_cast; ring
lemma OMA.a276key6 (m : ℕ) : a (m+6) = ((m+3).factorial : ℚ) * (m+4) * (m+5) *
    (harmonic (m+2) + 1/(m+3) + 1/(m+4) - 1) := by
  have h1 : a (m+6) = a ((m+2)+4) := rfl
  rw [h1, OMA.a276key, show m+2+3 = (m+3)+1+1 by omega, Nat.factorial_succ, Nat.factorial_succ,
    show m+2+2 = (m+2)+1+1 by omega, harmonic_succ, harmonic_succ]
  push_cast; ring
lemma OMA.a276key7 (m : ℕ) : a (m+7) = ((m+3).factorial : ℚ) * (m+4) * (m+5) * (m+6) *
    (harmonic (m+2) + 1/(m+3) + 1/(m+4) + 1/(m+5) - 1) := by
  have h1 : a (m+7) = a ((m+3)+4) := rfl
  rw [h1, OMA.a276key, show m+3+3 = (m+3)+1+1+1 by omega, Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ, show m+3+2 = (m+2)+1+1+1 by omega, harmonic_succ, harmonic_succ, harmonic_succ]
  push_cast; ring
theorem OMA.solution : type_of% @OMA.S_oeis_a000276.main := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m+6-1 = m+5 by omega, show m+6-2 = m+4 by omega, OMA.a276key6, OMA.a276key5, OMA.a276key]
    push_cast
    field_simp
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    rw [show m+7-1 = m+6 by omega, show m+7-2 = m+5 by omega, show m+7-3 = m+4 by omega,
      OMA.a276key7, OMA.a276key6, OMA.a276key5, OMA.a276key]
    push_cast
    field_simp
    ring
