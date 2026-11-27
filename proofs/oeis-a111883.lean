import OMAStatements.S_oeis_a111883
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a111883.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e3 : m + 3 - 3 = m := by omega
  rw [e1, e2, e3]
  have h3 : OMA.S_oeis_a111883.involutions (m + 3)
      = OMA.S_oeis_a111883.involutions (m + 2) + ((m : ℤ) + 2) * OMA.S_oeis_a111883.involutions (m + 1) := by
    rw [OMA.S_oeis_a111883.involutions]
    push_cast
    ring
  have h2 : OMA.S_oeis_a111883.involutions (m + 2)
      = OMA.S_oeis_a111883.involutions (m + 1) + ((m : ℤ) + 1) * OMA.S_oeis_a111883.involutions m := by
    rw [OMA.S_oeis_a111883.involutions]
  simp only [OMA.S_oeis_a111883.a]
  rw [h3, h2]
  push_cast
  ring
