import OMAReductions.R_Erdos1210_erdos_1210_R1

/-! For n ≤ 2 the set A is empty or {1} (and then n = 2), so the left side is at most 1, while the
right side is a sum of nonnegative terms plus 1. -/

theorem OMA.solution : OMA.R_Erdos1210_erdos_1210_R1.H1 := by
  intro n hn A hA _
  have hL : ∑ a ∈ A, (1 / ((n : ℝ) - a)) ≤ 1 := by
    have hsub : A ⊆ {1} := by
      intro a ha
      have := hA a ha
      rw [Finset.mem_singleton]
      omega
    rcases Finset.subset_singleton_iff.1 hsub with rfl | rfl
    · simp
    · have h1 := hA 1 (Finset.mem_singleton_self 1)
      have hn2 : (n : ℝ) = 2 := by exact_mod_cast (show n = 2 by omega)
      rw [Finset.sum_singleton, hn2]
      norm_num
  exact hL.trans (le_add_of_nonneg_left (Finset.sum_nonneg (fun p _ => by positivity)))
