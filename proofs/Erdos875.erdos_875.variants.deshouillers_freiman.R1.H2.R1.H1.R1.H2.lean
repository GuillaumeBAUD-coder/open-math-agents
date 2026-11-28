import OMAReductions.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H2_R1_H1_R1
import Mathlib

theorem OMA.e875_aux : ∀ n, ∀ B : Finset ℕ, B.card = n → ∀ r, r ≤ n →
    r * (n - r) + 1 ≤ ((B.powersetCard r).image (fun T => ∑ x ∈ T, x)).card := by
  intro n
  induction n with
  | zero =>
    intro B hB r hr
    have : r = 0 := by omega
    subst this
    simp
  | succ k ih =>
    intro B hB r hr
    rcases Nat.lt_or_ge k r with h | h
    · have hr' : r = k + 1 := by omega
      subst hr'
      simp only [Nat.sub_self, mul_zero, zero_add]
      rw [Finset.one_le_card]
      exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_powersetCard.mpr ⟨subset_rfl, hB⟩)⟩
    · have hne : B.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨M, hM⟩ : ∃ M, M = B.max' hne := ⟨_, rfl⟩
      have hMB : M ∈ B := hM ▸ B.max'_mem hne
      have hB' : (B.erase M).card = k := by rw [Finset.card_erase_of_mem hMB]; omega
      have ih' := ih (B.erase M) hB' r h
      have hne2 : (Finset.powersetCard r (B.erase M)).Nonempty :=
        Finset.powersetCard_nonempty.mpr (by omega)
      obtain ⟨U, hU, hmax⟩ := Finset.exists_max_image _ (fun T => ∑ x ∈ T, x) hne2
      rw [Finset.mem_powersetCard] at hU
      obtain ⟨S', hS'⟩ : ∃ S', S' = ((B.erase M).powersetCard r).image (fun T => ∑ x ∈ T, x) :=
        ⟨_, rfl⟩
      obtain ⟨N, hN⟩ : ∃ N, N = U.image (fun u => ∑ x ∈ U, x - u + M) := ⟨_, rfl⟩
      rw [← hS'] at ih'
      have hle : ∀ u ∈ U, u ≤ ∑ x ∈ U, x := fun u hu =>
        Finset.single_le_sum (f := fun x => x) (fun i _ => Nat.zero_le i) hu
      have hltM : ∀ u ∈ U, u < M := fun u hu =>
        lt_of_le_of_ne (hM ▸ B.le_max' u (Finset.mem_of_mem_erase (hU.1 hu)))
          (Finset.ne_of_mem_erase (hU.1 hu))
      have hNcard : N.card = r := by
        rw [hN, Finset.card_image_of_injOn, hU.2]
        intro u hu v hv huv
        have h1 := hle u hu
        have h2 := hle v hv
        try dsimp only at huv
        omega
      have hdisj : Disjoint S' N := by
        rw [Finset.disjoint_left]
        intro x hx hxN
        rw [hS'] at hx
        rw [hN] at hxN
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hxN
        have h1 := hmax T hT
        have h2 := hle u hu
        have h3 := hltM u hu
        try dsimp only at h1 hux
        omega
      have hsub : S' ∪ N ⊆ (B.powersetCard r).image (fun T => ∑ x ∈ T, x) := by
        apply Finset.union_subset
        · rw [hS']
          exact Finset.image_subset_image (Finset.powersetCard_mono (Finset.erase_subset _ _))
        · intro x hxN
          rw [hN] at hxN
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hxN
          have hMU : M ∉ U.erase u := fun hc =>
            Finset.notMem_erase M B (hU.1 (Finset.mem_of_mem_erase hc))
          refine Finset.mem_image.mpr ⟨insert M (U.erase u), ?_, ?_⟩
          · rw [Finset.mem_powersetCard]
            refine ⟨?_, ?_⟩
            · intro y hy
              rcases Finset.mem_insert.mp hy with rfl | hy
              · exact hMB
              · exact Finset.mem_of_mem_erase (hU.1 (Finset.mem_of_mem_erase hy))
            · rw [Finset.card_insert_of_notMem hMU, Finset.card_erase_of_mem hu, hU.2]
              have : 0 < U.card := Finset.card_pos.mpr ⟨u, hu⟩
              omega
          · rw [Finset.sum_insert hMU]
            have := Finset.add_sum_erase U (fun x => x) hu
            try dsimp only at this
            omega
      have hc := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, hNcard] at hc
      have e : r * (k + 1 - r) = r * (k - r) + r := by
        rw [show k + 1 - r = (k - r) + 1 by omega]; ring
      omega

theorem OMA.solution : OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H2_R1_H1_R1.H2 := by
  intro B r hr
  exact OMA.e875_aux B.card B rfl r hr
