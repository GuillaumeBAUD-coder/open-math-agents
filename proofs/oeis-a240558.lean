import OMAStatements.S_oeis_a240558
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a240558.main := by
  intro n hn
  simp only [OMA.S_oeis_a240558.a]
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [show 2 * (i + 1) - 1 = 2 * i + 1 by omega, show 2 * (i + 1) - 2 = 2 * i by omega,
      show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
    rw [show (2 * i + 1 + 1) / 2 = i + 1 by omega, show (2 * i + 1) / 2 = i by omega,
      show 2 * i / 2 = i by omega]
    simp only [Nat.factorial_succ, pow_succ]
    have : ((2 * i).factorial : ℚ) ≠ 0 := by positivity
    have : (i.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [show 2 * (i + 1) + 1 - 1 = 2 * i + 1 + 1 by omega,
      show 2 * (i + 1) + 1 - 2 = 2 * i + 1 by omega,
      show 2 * (i + 1) + 1 = 2 * i + 2 + 1 by ring]
    rw [show (2 * i + 2 + 1) / 2 = i + 1 by omega, show (2 * i + 1 + 1) / 2 = i + 1 by omega,
      show (2 * i + 1) / 2 = i by omega]
    simp only [Nat.factorial_succ, show 2 * i + 2 = 2 * i + 1 + 1 by ring, Nat.factorial_succ,
      pow_succ]
    have : ((2 * i).factorial : ℚ) ≠ 0 := by positivity
    have : (i.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
