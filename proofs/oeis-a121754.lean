import OMAStatements.S_oeis_a121754

-- Problem: A121754: Number of columns ending at an even level in all deco polyominoes of height n. A deco polyomino is a directed column-convex polyomino in which the height, measured along the diagonal, is attained only in the last column.
-- Upstream: formal-conjectures statements/oeis-a121754.lean:0 (declaration OMA.S_oeis_a121754.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Put b(m) = a(m) - m a(m-1). The defining recurrence gives b(m) = (m-3) b(m-1) + g(m), where g is
its factorial term, so b(m) = (m-3)! eta(m) for an explicit quasi-polynomial eta (induction on m).
The left side of the recurrence is a combination of five of these first-order relations, and what
remains is an identity between factorials and polynomials. -/

namespace A121754Aux

open OMA.S_oeis_a121754

theorem a_step (k : ℕ) : a (k + 3) =
    (2 * ((k : ℚ) + 3) - 3) * a (k + 2) - ((k : ℚ) + 3 - 1) * ((k : ℚ) + 3 - 3) * a (k + 1) +
      ((k + 1).factorial : ℚ) * ((k : ℚ) + 3 - 2 + (1 / 2) * (1 + (-1 : ℚ) ^ (k + 2)) * ((k : ℚ) + 3 - 1)) := by
  rw [a]

/-- The quasi-polynomial eta with a(m) - m a(m-1) = (m-3)! eta(m). -/
def eta (m : ℕ) : ℚ :=
  (-7 + 20 * (m : ℚ) - 16 * (m : ℚ) ^ 2 + 4 * (m : ℚ) ^ 3) / 8 + (-1 : ℚ) ^ m * ((-1 + 4 * (m : ℚ) - 2 * (m : ℚ) ^ 2) / 8)

theorem first (k : ℕ) :
    a (k + 3) - ((k : ℚ) + 3) * a (k + 2) = (k.factorial : ℚ) * eta (k + 3) := by
  induction k with
  | zero =>
    have h := a_step 0
    norm_num [a, eta] at h ⊢ <;> linarith
  | succ k ih =>
    have h1 := a_step (k + 1)
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.factorial_succ, eta] at h1 ih ⊢
    push_cast at h1 ih ⊢
    linear_combination h1 + ((k : ℚ) + 1) * ih

end A121754Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a121754.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 from rfl, show m + 6 - 2 = m + 4 from rfl, show m + 6 - 3 = m + 3 from rfl,
    show m + 6 - 4 = m + 2 from rfl, show m + 6 - 5 = m + 1 from rfl]
  rcases m with _ | j
  · norm_num [OMA.S_oeis_a121754.a, Nat.factorial]
  · have B4 := A121754Aux.first (j + 4)
    have B3 := A121754Aux.first (j + 3)
    have B2 := A121754Aux.first (j + 2)
    have B1 := A121754Aux.first (j + 1)
    have B0 := A121754Aux.first j
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.factorial_succ, A121754Aux.eta] at B4 B3 B2 B1 B0 ⊢
    push_cast at B4 B3 B2 B1 B0 ⊢
    linear_combination (16 + 16 * ((j : ℚ) + 7)) * B4 + (531 - 162 * ((j : ℚ) + 7)) * B3 +
      (-1041 + 300 * ((j : ℚ) + 7) + 16 * ((j : ℚ) + 7) ^ 2 - 16 * ((j : ℚ) + 7) ^ 3) * B2 + (-1541 + 2581 * ((j : ℚ) + 7) - 1171 * ((j : ℚ) + 7) ^ 2 + 146 * ((j : ℚ) + 7) ^ 3) * B1 +
      (7464 - 6230 * ((j : ℚ) + 7) + 1611 * ((j : ℚ) + 7) ^ 2 - 130 * ((j : ℚ) + 7) ^ 3) * B0
