import OMAReductions.R_Erdos165_erdos_165_variants_lower_R1
import Mathlib

/-! Ramsey finiteness for R(3, k), with the classical bound R(3, k) ≤ k * k from the induction R(3, k + 1) ≤ R(3, k) + k + 1. -/

open SimpleGraph

theorem OMA.r3k_finset {V : Type*} [DecidableEq V] (C : SimpleGraph V) [DecidableRel C.Adj] :
    ∀ k : ℕ, ∀ s : Finset V, k * k ≤ s.card →
      (∃ t ⊆ s, C.IsNClique 3 t) ∨ (∃ t ⊆ s, Cᶜ.IsNClique k t) := by
  intro k
  induction k with
  | zero =>
    intro s _
    exact Or.inr ⟨∅, Finset.empty_subset _, by simp [isNClique_iff, IsClique]⟩
  | succ k ih =>
    intro s hs
    have hpos : 0 < s.card := by nlinarith
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    let N := (s.erase v).filter (fun x => C.Adj v x)
    let M := (s.erase v).filter (fun x => ¬ C.Adj v x)
    have hNs : N ⊆ s := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
    have hMs : M ⊆ s := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
    by_cases hN : k + 1 ≤ N.card
    · by_cases hind : (N : Set V).Pairwise (fun x y => ¬ C.Adj x y)
      · obtain ⟨t, htN, htc⟩ := Finset.exists_subset_card_eq hN
        refine Or.inr ⟨t, htN.trans hNs, ?_, htc⟩
        intro x hx y hy hxy
        rw [compl_adj]
        exact ⟨hxy, hind (htN hx) (htN hy) hxy⟩
      · simp only [Set.Pairwise, not_forall, not_not] at hind
        obtain ⟨a, ha, b, hb, hab, hadj⟩ := hind
        have ha' : C.Adj v a := (Finset.mem_filter.mp ha).2
        have hb' : C.Adj v b := (Finset.mem_filter.mp hb).2
        refine Or.inl ⟨{v, a, b}, ?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact hv
          · exact hNs ha
          · exact hNs hb
        · rw [is3Clique_triple_iff]
          exact ⟨ha', hb', hadj⟩
    · push Not at hN
      have hsplit := Finset.card_filter_add_card_filter_not (s := s.erase v)
          (fun x => C.Adj v x)
      have herase := Finset.card_erase_of_mem hv
      have hM : k * k ≤ M.card := by
        have : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
        change N.card + M.card = (s.erase v).card at hsplit
        omega
      rcases ih M hM with ⟨t, htM, ht⟩ | ⟨t, htM, ht⟩
      · exact Or.inl ⟨t, htM.trans hMs, ht⟩
      · refine Or.inr ⟨insert v t, Finset.insert_subset hv (htM.trans hMs), ?_⟩
        apply ht.insert
        intro b hb
        have hbM := Finset.mem_filter.mp (htM hb)
        rw [compl_adj]
        exact ⟨(Finset.ne_of_mem_erase hbM.1).symm, hbM.2⟩

theorem OMA.solution : OMA.R_Erdos165_erdos_165_variants_lower_R1.H1 := by
  intro k
  refine ⟨k * k, fun C => ?_⟩
  classical
  rcases OMA.r3k_finset C k Finset.univ (by simp) with ⟨t, -, ht⟩ | ⟨t, -, ht⟩
  · left
    rw [← not_cliqueFree_iff_top_isContained]
    exact fun h => h t ht
  · right
    rw [← not_cliqueFree_iff_top_isContained]
    exact fun h => h t ht
