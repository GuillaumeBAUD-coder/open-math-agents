import FormalConjectures.OptimizationConstants.«6a»

-- Credit: @aspher1
-- The family consisting of the empty set and one singleton bounds the density by one half.

theorem OMA.solution : type_of% @Constant6a.c6a_upper_bound := by
  unfold Constant6a.C6a
  apply csSup_le
  · refine ⟨0, ?_⟩
    intro A _ _
    exact ⟨0, by simp⟩
  · intro c hc
    obtain ⟨i, hi⟩ := hc ({∅, {0}} : Finset (Finset ℕ)) (by decide) (by decide)
    by_cases hi0 : i = 0
    · simp [Finset.filter_insert, Finset.filter_singleton, hi0] at hi
      linarith
    · simp [Finset.filter_insert, Finset.filter_singleton, hi0] at hi
      linarith
