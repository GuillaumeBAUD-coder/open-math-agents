import OMAStatements.S_oeis_a121580

-- Problem: A121580: Number of cells in column 1 of all deco polyominoes of height n. A deco polyomino is a directed column-convex polyomino in which the height, measured along the diagonal, is attained only in the last column.
-- Upstream: formal-conjectures statements/oeis-a121580.lean:0 (declaration OMA.S_oeis_a121580.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! For n ≥ 5 the defining recurrence a(k) = a(k-1) + (k-1)! (1 + k(k-1)/2) applies to a(n), a(n-1),
a(n-2) and a(n-3). Substituting these four instances expresses the left side through a(n-4) and
factorials, and it vanishes identically. -/

namespace A121580Aux

open OMA.S_oeis_a121580

theorem a_step (k : ℕ) : a (k + 2) =
    a (k + 1) + ((k + 1).factorial : ℚ) * (1 + ((k : ℚ) + 2) * ((k : ℚ) + 1) / 2) := by
  rw [a]

end A121580Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a121580.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 + 2 := ⟨n - 5, by omega⟩
  have e1 : m + 3 + 2 - 1 = m + 2 + 2 := rfl
  have e2 : m + 3 + 2 - 2 = m + 1 + 2 := rfl
  have e3 : m + 3 + 2 - 3 = m + 2 := rfl
  have e4 : m + 3 + 2 - 4 = m + 1 := rfl
  rw [e1, e2, e3, e4]
  have h5 := A121580Aux.a_step (m + 3)
  have h4 := A121580Aux.a_step (m + 2)
  have h3 := A121580Aux.a_step (m + 1)
  have h2 := A121580Aux.a_step m
  simp only [Nat.factorial_succ] at h5 h4 h3 h2
  push_cast at h5 h4 h3 h2 ⊢
  linear_combination h5 + (-((m : ℚ) + 5) - 3) * h4 + (2 * ((m : ℚ) + 5)) * h3 +
    (6 - 2 * ((m : ℚ) + 5)) * h2
