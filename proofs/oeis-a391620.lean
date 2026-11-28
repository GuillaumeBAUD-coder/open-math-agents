import OMAStatements.S_oeis_a391620

open OMA.S_oeis_a391620

theorem B : ∀ l : List ℕ, l.Pairwise (· ≥ ·) → (∀ x ∈ l, 4 ≤ x) →
    ∃ h t, (∀ x ∈ h :: t, 1 < x) ∧ firstSums (h :: t) = l ∧ h + 2 ≤ l.headD 4
  | [], _, _ => ⟨2, [], by simp, rfl, le_rfl⟩
  | y :: l, hp, h4 => by
    simp at hp h4
    obtain ⟨h, t, h1, h2, h3⟩ := B l hp.2 h4.2
    refine ⟨y - h, h :: t, ?_, by simp_all [firstSums]; cases l <;> simp_all <;> omega, by simp at h1 ⊢; omega⟩
    cases l <;> simp_all <;> grind

theorem OMA.solution : type_of% @OMA.S_oeis_a391620.main := by
  refine fun n _ y => ⟨fun h => ?_, fun ⟨x, hx, h4⟩ ⟨c, _, hc, hf⟩ => ?_⟩
  · by_contra H
    obtain ⟨a, t, h1, h2, -⟩ := B _ (Multiset.pairwise_sort _ _) (by simpa [partsDesc] using H)
    exact h ⟨_, by simp, h1, h2⟩
  · have : x ∈ firstSums c := hf ▸ (Multiset.mem_sort _).2 hx
    simp only [firstSums, ← List.map_uncurry_zip_eq_zipWith, List.mem_map] at this
    obtain ⟨⟨a, b⟩, hm, rfl⟩ := this
    have z := List.of_mem_zip hm
    have := hc a z.1; have := hc b (List.mem_of_mem_tail z.2)
    simp at h4; omega
