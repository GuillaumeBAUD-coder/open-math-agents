import OMAStatements.S_oeis_a193282
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a193282.main := by
  intro n hn
  simp only [OMA.S_oeis_a193282.a]
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    rw [show 2 * (i + 2) - 1 = 2 * i + 2 + 1 by omega, show 2 * (i + 2) - 2 = 2 * i + 1 + 1 by omega,
      show 2 * (i + 2) - 3 = 2 * i + 1 by omega, show 2 * (i + 2) - 4 = 2 * i by omega,
      show 2 * (i + 2) = 2 * i + 3 + 1 by ring]
    rw [show (2 * i + 3 + 1) / 2 = i + 1 + 1 by omega, show (2 * i + 2 + 1) / 2 = i + 1 by omega,
      show (2 * i + 1 + 1) / 2 = i + 1 by omega, show (2 * i + 1) / 2 = i by omega,
      show 2 * i / 2 = i by omega]
    simp only [Nat.factorial_succ, show 2 * i + 3 = 2 * i + 2 + 1 by ring,
      show 2 * i + 2 = 2 * i + 1 + 1 by ring, Nat.factorial_succ]
    have : ((2 * i).factorial : ℚ) ≠ 0 := by positivity
    have : (i.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    rw [show 2 * (i + 2) + 1 - 1 = 2 * i + 3 + 1 by omega,
      show 2 * (i + 2) + 1 - 2 = 2 * i + 2 + 1 by omega,
      show 2 * (i + 2) + 1 - 3 = 2 * i + 1 + 1 by omega, show 2 * (i + 2) + 1 - 4 = 2 * i + 1 by omega,
      show 2 * (i + 2) + 1 = 2 * i + 4 + 1 by ring]
    rw [show (2 * i + 4 + 1) / 2 = i + 1 + 1 by omega, show (2 * i + 3 + 1) / 2 = i + 1 + 1 by omega,
      show (2 * i + 2 + 1) / 2 = i + 1 by omega, show (2 * i + 1 + 1) / 2 = i + 1 by omega,
      show (2 * i + 1) / 2 = i by omega]
    simp only [Nat.factorial_succ, show 2 * i + 4 = 2 * i + 3 + 1 by ring,
      show 2 * i + 3 = 2 * i + 2 + 1 by ring,
      show 2 * i + 2 = 2 * i + 1 + 1 by ring, Nat.factorial_succ]
    have : ((2 * i + 1).factorial : ℚ) ≠ 0 := by positivity
    have : (i.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
