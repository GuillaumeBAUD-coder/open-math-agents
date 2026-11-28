import OMAStatements.S_oeis_a261681
import Mathlib

lemma OMA.ch (b c : ℕ) : ((b + c).choose b : ℚ) = (b + c).factorial / (b.factorial * c.factorial) :=
  Nat.cast_add_choose ℚ

theorem OMA.solution : type_of% @OMA.S_oeis_a261681.main := by
  intro n hn
  simp only [OMA.S_oeis_a261681.a]
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    rw [show 2 * (i + 2) - 1 = (i + 1) + (i + 2) by omega,
      show 2 * (i + 2) - 2 = (i + 1) + (i + 1) by omega,
      show 2 * (i + 2) - 3 = i + (i + 1) by omega, show 2 * (i + 2) - 4 = i + i by omega,
      show 2 * (i + 2) = (i + 2) + (i + 2) by ring]
    rw [show (i + 2 + (i + 2)) / 2 = i + 2 by omega, show (i + 1 + (i + 2)) / 2 = i + 1 by omega,
      show (i + 1 + (i + 1)) / 2 = i + 1 by omega, show (i + (i + 1)) / 2 = i by omega,
      show (i + i) / 2 = i by omega]
    qify
    simp only [OMA.ch]
    simp only [show i + 2 + (i + 2) = (i + i) + 3 + 1 by ring,
      show i + 1 + (i + 2) = (i + i) + 2 + 1 by ring,
      show i + 1 + (i + 1) = (i + i) + 1 + 1 by ring, show i + (i + 1) = (i + i) + 1 by ring,
      show i + 2 = i + 1 + 1 by ring, show (i + i) + 3 = (i + i) + 2 + 1 by ring,
      show (i + i) + 2 = (i + i) + 1 + 1 by ring, Nat.factorial_succ, pow_succ]
    have : ((i + i).factorial : ℚ) ≠ 0 := by positivity
    have : (i.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    rw [show 2 * (i + 2) + 1 - 1 = (i + 2) + (i + 2) by omega,
      show 2 * (i + 2) + 1 - 2 = (i + 1) + (i + 2) by omega,
      show 2 * (i + 2) + 1 - 3 = (i + 1) + (i + 1) by omega,
      show 2 * (i + 2) + 1 - 4 = i + (i + 1) by omega,
      show 2 * (i + 2) + 1 = (i + 2) + (i + 3) by ring]
    rw [show (i + 2 + (i + 3)) / 2 = i + 2 by omega, show (i + 2 + (i + 2)) / 2 = i + 2 by omega,
      show (i + 1 + (i + 2)) / 2 = i + 1 by omega,
      show (i + 1 + (i + 1)) / 2 = i + 1 by omega, show (i + (i + 1)) / 2 = i by omega]
    qify
    simp only [OMA.ch]
    simp only [show i + 2 + (i + 3) = (i + i) + 4 + 1 by ring,
      show i + 2 + (i + 2) = (i + i) + 3 + 1 by ring,
      show i + 1 + (i + 2) = (i + i) + 2 + 1 by ring,
      show i + 1 + (i + 1) = (i + i) + 1 + 1 by ring, show i + (i + 1) = (i + i) + 1 by ring,
      show i + 3 = i + 2 + 1 by ring, show i + 2 = i + 1 + 1 by ring,
      show (i + i) + 4 = (i + i) + 3 + 1 by ring,
      show (i + i) + 3 = (i + i) + 2 + 1 by ring,
      show (i + i) + 2 = (i + i) + 1 + 1 by ring, Nat.factorial_succ, pow_succ]
    have : ((i + i).factorial : ℚ) ≠ 0 := by positivity
    have : (i.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
