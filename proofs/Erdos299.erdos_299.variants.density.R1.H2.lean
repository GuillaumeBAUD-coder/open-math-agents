import OMAReductions.R_Erdos299_erdos_299_variants_density_R1

-- Step Erdos299.erdos_299.variants.density.R1.H2: hypothesis H2 of reduction Erdos299.erdos_299.variants.density.R1
-- Credit: @loremcdmx
-- H2 := ∀ (A : Set ℕ) (w : ℕ → ℝ) (r : ℝ),     (∃ᶠ N : ℕ in atTop, ∃ S : Finset ℕ,       (↑S : Set ℕ) ⊆ A ∩ Set.Ici N ∧ ∑ n ∈ S, w n = r) →     ∀ k : ℕ, ∃ T : Finset ℕ, (↑T : Set ℕ) ⊆ A ∧ ∑ n ∈ T, w n = k * r

open Filter

theorem OMA.solution : OMA.R_Erdos299_erdos_299_variants_density_R1.H2 := by
  intro A w r hf k
  induction k with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨T, hT, hsum⟩ := ih
    obtain ⟨N, hN, S, hS, hSr⟩ := Filter.frequently_atTop.mp hf (T.sup id + 1)
    have hdisj : Disjoint T S := by
      rw [Finset.disjoint_left]
      intro x hx hxS
      have h1 : x ≤ T.sup id := Finset.le_sup (f := id) hx
      have h2 : N ≤ x := (hS hxS).2
      omega
    refine ⟨T ∪ S, ?_, ?_⟩
    · rw [Finset.coe_union]
      exact Set.union_subset hT (fun x hx => (hS hx).1)
    · rw [Finset.sum_union hdisj, hsum, hSr]
      push_cast
      ring
