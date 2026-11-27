import OMAReductions.R_Erdos298_erdos_298_variants_natural_density_R1

theorem OMA.solution : OMA.R_Erdos298_erdos_298_variants_natural_density_R1.H2 := by
  intro A w r hfreq k
  induction k with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨T, hTA, hT⟩ := ih
    obtain ⟨N, hN, S, hS, hSr⟩ := (Filter.frequently_atTop.1 hfreq) (T.sup id + 1)
    have hdisj : Disjoint T S := by
      rw [Finset.disjoint_left]
      intro x hxT hxS
      have h1 : x ≤ T.sup id := Finset.le_sup (f := id) hxT
      have h2 : N ≤ x := (hS (Finset.mem_coe.2 hxS)).2
      omega
    refine ⟨T ∪ S, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with h | h
      · exact hTA (Finset.mem_coe.2 h)
      · exact (hS (Finset.mem_coe.2 h)).1
    · rw [Finset.sum_union hdisj, hT, hSr]
      push_cast
      ring
