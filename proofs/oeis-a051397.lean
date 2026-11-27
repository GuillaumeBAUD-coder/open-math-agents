import OMAStatements.S_oeis_a051397
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a051397.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  have e2 : OMA.S_oeis_a051397.a (m + 2) =
      2 * ((m + 1 : ℕ) : ℤ) * (2 * ((m + 1 : ℕ) : ℤ) + 1) * OMA.S_oeis_a051397.a (m + 1) + 1 := rfl
  have e1 : OMA.S_oeis_a051397.a (m + 1) =
      2 * (m : ℤ) * (2 * (m : ℤ) + 1) * OMA.S_oeis_a051397.a m + 1 := rfl
  rw [e2]
  push_cast
  linear_combination (-1 : ℤ) * e1
