import OMAStatements.S_oeis_a000276
import Mathlib

-- Problem: oeis-a000276
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P000276
open OMA.S_oeis_a000276

lemma e (k : ℕ) : a (k + 2) = ((k + 1).factorial : ℚ) * (harmonic k - 1) := by
  simp [a]

theorem sol : type_of% @OMA.S_oeis_a000276.main := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    have h1 : a (m + 6) = ((m + 5).factorial : ℚ) * (harmonic (m + 4) - 1) := e (m + 4)
    have h2 : a (m + 6 - 1) = ((m + 4).factorial : ℚ) * (harmonic (m + 3) - 1) := by
      rw [show m + 6 - 1 = (m + 3) + 2 by omega]; exact e _
    have h3 : a (m + 6 - 2) = ((m + 3).factorial : ℚ) * (harmonic (m + 2) - 1) := by
      rw [show m + 6 - 2 = (m + 2) + 2 by omega]; exact e _
    rw [h1, h2, h3, Nat.factorial_succ (m + 4), Nat.factorial_succ (m + 3),
      harmonic_succ (m + 3), harmonic_succ (m + 2)]
    have h : ((m + 3).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have h1 : a (m + 7) = ((m + 6).factorial : ℚ) * (harmonic (m + 5) - 1) := e (m + 5)
    have h2 : a (m + 7 - 1) = ((m + 5).factorial : ℚ) * (harmonic (m + 4) - 1) := by
      rw [show m + 7 - 1 = (m + 4) + 2 by omega]; exact e _
    have h3 : a (m + 7 - 2) = ((m + 4).factorial : ℚ) * (harmonic (m + 3) - 1) := by
      rw [show m + 7 - 2 = (m + 3) + 2 by omega]; exact e _
    have h4 : a (m + 7 - 3) = ((m + 3).factorial : ℚ) * (harmonic (m + 2) - 1) := by
      rw [show m + 7 - 3 = (m + 2) + 2 by omega]; exact e _
    rw [h1, h2, h3, h4, Nat.factorial_succ (m + 5), Nat.factorial_succ (m + 4),
      Nat.factorial_succ (m + 3),
      harmonic_succ (m + 4), harmonic_succ (m + 3), harmonic_succ (m + 2)]
    have h : ((m + 3).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

end OMA.P000276

theorem OMA.solution : type_of% @OMA.S_oeis_a000276.main := OMA.P000276.sol
