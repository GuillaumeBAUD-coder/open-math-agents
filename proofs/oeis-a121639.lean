import OMAStatements.S_oeis_a121639

-- Problem: A121639: Number of 2-cell columns in all deco polyominoes of height n. A deco polyomino is a directed column-convex polyomino in which the height, measured along the diagonal, is attained only in the last column.
-- Upstream: formal-conjectures statements/oeis-a121639.lean:0 (declaration OMA.S_oeis_a121639.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! For n ≥ 7 the defining recurrence a(k) = k a(k-1) + (k-1)! - (k-3)! applies to a(n), a(n-1),
a(n-2) and a(n-3). Substituting these four instances expresses the left side through a(n-4) and
factorials, and it vanishes identically. -/

namespace A121639Aux

open OMA.S_oeis_a121639

theorem a_step (k : ℕ) : a (k + 4) =
    ((k : ℤ) + 4) * a (k + 3) + ((k + 3).factorial : ℤ) - ((k + 1).factorial : ℤ) := by
  rw [a]

end A121639Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a121639.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 + 4 := ⟨n - 7, by omega⟩
  have e1 : m + 3 + 4 - 1 = m + 2 + 4 := rfl
  have e2 : m + 3 + 4 - 2 = m + 1 + 4 := rfl
  have e3 : m + 3 + 4 - 3 = m + 4 := rfl
  have e4 : m + 3 + 4 - 4 = m + 3 := rfl
  rw [e1, e2, e3, e4]
  have h7 := A121639Aux.a_step (m + 3)
  have h6 := A121639Aux.a_step (m + 2)
  have h5 := A121639Aux.a_step (m + 1)
  have h4 := A121639Aux.a_step m
  simp only [Nat.factorial_succ] at h7 h6 h5 h4
  push_cast at h7 h6 h5 h4 ⊢
  linear_combination h7 + (1 - ((m : ℤ) + 7)) * h6 - h5 + (((m : ℤ) + 7) - 5) * h4
