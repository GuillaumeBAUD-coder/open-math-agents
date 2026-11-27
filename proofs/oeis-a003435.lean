import OMAStatements.S_oeis_a003435
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a003435.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega]
  have e5 : OMA.S_oeis_a003435.a (k + 5) =
      (2 * ((k + 1 : ℕ) + 4 : ℚ) * (4 * ((k + 1 : ℕ) + 4 : ℚ) ^ 2 - 8 * ((k + 1 : ℕ) + 4 : ℚ) + 5) *
          OMA.S_oeis_a003435.a (k + 4) +
        4 * (((k + 1 : ℕ) + 4 : ℚ) - 1) * ((k + 1 : ℕ) + 4 : ℚ) * (2 * ((k + 1 : ℕ) + 4 : ℚ) - 1) *
          OMA.S_oeis_a003435.a (k + 3)) / (2 * ((k + 1 : ℕ) + 4 : ℚ) - 3) := rfl
  have e4 : OMA.S_oeis_a003435.a (k + 4) =
      (2 * ((k : ℕ) + 4 : ℚ) * (4 * ((k : ℕ) + 4 : ℚ) ^ 2 - 8 * ((k : ℕ) + 4 : ℚ) + 5) *
          OMA.S_oeis_a003435.a (k + 3) +
        4 * (((k : ℕ) + 4 : ℚ) - 1) * ((k : ℕ) + 4 : ℚ) * (2 * ((k : ℕ) + 4 : ℚ) - 1) *
          OMA.S_oeis_a003435.a (k + 2)) / (2 * ((k : ℕ) + 4 : ℚ) - 3) := rfl
  rw [e5, e4]
  push_cast
  have hk : (0 : ℚ) ≤ k := by positivity
  have h1 : (2 * ((k : ℚ) + 1 + 4) - 3) ≠ 0 := by
    intro h; linarith
  have h2 : (2 * ((k : ℚ) + 4) - 3) ≠ 0 := by
    intro h; linarith
  field_simp
  ring
