import OMAStatements.S_oeis_a080958

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: first-order relations for a(n) and auxiliary sums (sum splitting, Pascal rule),
-- combined by linear_combination into the stated recurrence.

open OMA.S_oeis_a080958

namespace P_oeis_a080958

lemma a_succ (n : ℕ) :
    a (n + 1) = ((n : ℚ) + 1) * a n + ((n : ℚ) + 2) * ((-1 : ℚ) ^ n * (n.factorial : ℚ)) := by
  unfold a
  rw [Finset.sum_Icc_succ_top (by omega), Nat.factorial_succ]
  push_cast
  have h : ((n : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem main_proved : ∀ n : ℕ, 2 ≤ n →
    -((n : ℚ) + 1) * a (n + 1) + a n + (n : ℚ) ^ 2 * ((n : ℚ) + 2) * a (n - 1) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 := a_succ k
  have h2 := a_succ (k + 1)
  rw [Nat.factorial_succ, pow_succ] at h2
  push_cast at h1 h2 ⊢
  rw [h2, h1]
  ring

end P_oeis_a080958

theorem OMA.solution : type_of% @OMA.S_oeis_a080958.main := P_oeis_a080958.main_proved
