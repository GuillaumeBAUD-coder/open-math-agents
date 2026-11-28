import OMAReductions.R_Erdos142_erdos_142_variants_lower_R4

open Erdos142

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R4.H2 := by
  intro N
  unfold r Set.IsAPOfLengthFree.maxCard
  apply csSup_le
  · refine ⟨0, ∅, by simp, ?_, Finset.card_empty⟩
    intro T hT hAP
    have he : T = ∅ := Set.eq_empty_of_subset_empty (by simpa using hT)
    subst T
    exact (Set.not_isAPOfLength_empty (by decide) hAP).elim
  · rintro m ⟨S, -, hfree, rfl⟩
    by_contra! hc
    obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp hc
    have noPair {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) : False := by
      have hs : ({x, y} : Set ℕ) ⊆ (S : Set ℕ) :=
        Set.insert_subset_iff.mpr ⟨hx, Set.singleton_subset_iff.mpr hy⟩
      exact (by decide : ¬ (2 : ℕ∞) ≤ 1) (hfree _ hs (Nat.isAPOfLength_pair hxy))
    exact (lt_or_gt_of_ne hne).elim (noPair ha hb) (noPair hb ha)
