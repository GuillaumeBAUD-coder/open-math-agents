import OMAStatements.S_oeis_a121636

-- Problem: A121636: Number of 2-cell columns starting at level 0 in all of deco polyominoes of height n. A deco polyomino is a directed column-convex polyomino in which the height, measured along the diagonal, is attained only in the last column.
-- Upstream: formal-conjectures statements/oeis-a121636.lean:0 (declaration OMA.S_oeis_a121636.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! For n ≥ 5 the defining recurrence a(k) = k (k-2)! + (k-1) a(k-1) applies to a(n), a(n-1) and
a(n-2). Substituting these three instances expresses the left side through a(n-3) and factorials, and
it vanishes identically. -/

namespace A121636Aux

open OMA.S_oeis_a121636

theorem a_step (k : ℕ) : a (k + 3) =
    ((k : ℤ) + 3) * ((k + 1).factorial : ℤ) + ((k : ℤ) + 2) * a (k + 2) := by
  rw [a]

end A121636Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a121636.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 + 3 := ⟨n - 5, by omega⟩
  have e1 : m + 2 + 3 - 1 = m + 1 + 3 := rfl
  have e2 : m + 2 + 3 - 2 = m + 3 := rfl
  have e3 : m + 2 + 3 - 3 = m + 2 := rfl
  rw [e1, e2, e3]
  have h5 := A121636Aux.a_step (m + 2)
  have h4 := A121636Aux.a_step (m + 1)
  have h3 := A121636Aux.a_step m
  simp only [Nat.factorial_succ] at h5 h4 h3
  push_cast at h5 h4 h3 ⊢
  linear_combination h5 + (2 - ((m : ℤ) + 5)) * h4 + (3 - ((m : ℤ) + 5)) * h3
