import OMAStatements.S_oeis_a002735
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a002735.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
  have e2 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
  have key : OMA.S_oeis_a002735.B ((2 * m + 1) + 2) 2
      = 4 * OMA.S_oeis_a002735.B ((2 * m + 1) + 1) 2 := by
    rw [OMA.S_oeis_a002735.B]
    have hodd : ¬ ((2 * m + 1 + 2) % 2 = 0) := by omega
    rw [if_neg hodd]
    norm_num
  unfold OMA.S_oeis_a002735.a
  rw [e1, key, ← e2]
