import OMAReductions.R_Erdos298_erdos_298_variants_natural_density_R1

-- Step Erdos298.erdos_298.variants.natural_density.R1.H2: hypothesis H2 of reduction Erdos298.erdos_298.variants.natural_density.R1

/-!
Induction on `k`. Given `T ⊆ A` with weight `k r`, pick `N` above every element of `T`. Since sets
of weight `r` inside `A ∩ [N', ∞)` exist for arbitrarily large `N'`, there is one with `N' ≥ N`; it
is disjoint from `T`, and the union has weight `(k + 1) r`.
-/

theorem OMA.solution : OMA.R_Erdos298_erdos_298_variants_natural_density_R1.H2 := by
  unfold OMA.R_Erdos298_erdos_298_variants_natural_density_R1.H2
  intro A w r hfreq k
  induction k with
  | zero =>
    exact ⟨∅, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨T, hTA, hTsum⟩ := ih
    obtain ⟨N', hN', S, hSA, hSsum⟩ :=
      (Filter.frequently_atTop.mp hfreq) (T.sup id + 1)
    have hdisj : Disjoint T S := by
      rw [Finset.disjoint_left]
      intro x hxT hxS
      have h1 : x ≤ T.sup id := Finset.le_sup (f := id) hxT
      have h2 : N' ≤ x := (hSA (Finset.mem_coe.mpr hxS)).2
      omega
    refine ⟨T ∪ S, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with h | h
      · exact hTA (Finset.mem_coe.mpr h)
      · exact (hSA (Finset.mem_coe.mpr h)).1
    · rw [Finset.sum_union hdisj, hTsum, hSsum]
      push_cast
      ring
