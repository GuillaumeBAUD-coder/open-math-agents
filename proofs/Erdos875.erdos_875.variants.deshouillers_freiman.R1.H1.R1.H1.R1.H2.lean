import OMAReductions.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H1_R1_H1_R1
import Mathlib

theorem OMA.e875_sums (B : Finset ℕ) : ∀ r : ℕ, r ≤ B.card →
    r * (B.card - r) + 1 ≤ ((B.powersetCard r).image (fun T => ∑ x ∈ T, x)).card := by
  classical
  induction B using Finset.induction_on_max with
  | empty =>
    intro r hr
    have : r = 0 := by simpa using hr
    subst this
    simp
  | insert M s hM ih =>
    intro r hr
    have hMs : M ∉ s := fun h => lt_irrefl _ (hM M h)
    rw [Finset.card_insert_of_notMem hMs] at hr ⊢
    by_cases hrs : r ≤ s.card
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hrs
      have ih' := ih r hrs
      obtain ⟨T', hT', hmax⟩ := Finset.exists_max_image (s.powersetCard r)
        (fun T => ∑ x ∈ T, x) (Finset.powersetCard_nonempty.mpr hrs)
      rw [Finset.mem_powersetCard] at hT'
      have hle : ∀ t ∈ T', t ≤ ∑ x ∈ T', x := fun t ht =>
        Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) ht
      have hJ : (T'.image (fun t => (∑ x ∈ T', x) - t + M)).card = r := by
        rw [Finset.card_image_of_injOn, hT'.2]
        intro a ha b hb hab
        have h1 := hle a ha
        have h2 := hle b hb
        have hab' : (∑ x ∈ T', x) - a + M = (∑ x ∈ T', x) - b + M := hab
        omega
      have hdisj : Disjoint ((s.powersetCard r).image (fun T => ∑ x ∈ T, x))
          (T'.image (fun t => (∑ x ∈ T', x) - t + M)) := by
        rw [Finset.disjoint_left]
        intro v hv hv'
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hv'
        have h1 : ∑ x ∈ T, x ≤ ∑ x ∈ T', x := hmax T hT
        have h2 := hle t ht
        have h3 := hM t (hT'.1 ht)
        have he' : (∑ x ∈ T', x) - t + M = ∑ x ∈ T, x := he
        omega
      have hsub : ((s.powersetCard r).image (fun T => ∑ x ∈ T, x)) ∪
          (T'.image (fun t => (∑ x ∈ T', x) - t + M)) ⊆
          ((insert M s).powersetCard r).image (fun T => ∑ x ∈ T, x) := by
        intro v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hv
          rw [Finset.mem_powersetCard] at hT
          exact Finset.mem_image.mpr ⟨T, Finset.mem_powersetCard.mpr
            ⟨hT.1.trans (Finset.subset_insert _ _), hT.2⟩, rfl⟩
        · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
          have hMe : M ∉ T'.erase t := fun h => hMs (hT'.1 (Finset.mem_of_mem_erase h))
          refine Finset.mem_image.mpr ⟨insert M (T'.erase t), Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
          · exact Finset.insert_subset_insert _ ((Finset.erase_subset _ _).trans hT'.1)
          · rw [Finset.card_insert_of_notMem hMe, Finset.card_erase_of_mem ht, hT'.2]
            have : 0 < T'.card := Finset.card_pos.mpr ⟨t, ht⟩
            omega
          · show ∑ x ∈ insert M (T'.erase t), x = (∑ x ∈ T', x) - t + M
            rw [Finset.sum_insert hMe]
            have h5 : ∑ x ∈ T'.erase t, x + t = ∑ x ∈ T', x :=
              Finset.sum_erase_add T' (fun x => x) ht
            omega
      have hc := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, hJ] at hc
      have e1 : s.card + 1 - r = d + 1 := by omega
      have e2 : s.card - r = d := by omega
      rw [e1]
      rw [e2] at ih'
      have : r * (d + 1) = r * d + r := by ring
      omega
    · have hr' : r = s.card + 1 := by omega
      have hne : ((insert M s).powersetCard r).Nonempty :=
        Finset.powersetCard_nonempty.mpr (by rw [Finset.card_insert_of_notMem hMs]; omega)
      have := Finset.card_pos.mpr (hne.image (fun T => ∑ x ∈ T, x))
      rw [hr'] at this ⊢
      simp only [Nat.sub_self, Nat.mul_zero]
      omega

theorem OMA.solution : OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H1_R1_H1_R1.H2 := by
  intro B r hr
  exact OMA.e875_sums B r hr
