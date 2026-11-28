import OMAReductions.R_SumnerUniversalTournamentConjecture_sumner_conjecture_variants_large_n_R1_H2_R1
import Mathlib

open SimpleGraph in
theorem OMA.sumner_acyc {W : Type} (D : Digraph W) (T : SimpleGraph W) (hT : T.IsAcyclic)
    (hO : D.IsOrientation T) (u v : W) (huv : D.Adj u v) :
    ¬ Relation.ReflTransGen D.Adj v u := by
  intro hR
  have hb : T.IsBridge s(u, v) := isAcyclic_iff_forall_adj_isBridge.mp hT (hO.1 u v huv)
  rw [isBridge_iff] at hb
  have key : ∀ x, Relation.ReflTransGen D.Adj v x →
      (T.deleteEdges {s(u, v)}).Reachable v x ∨ (T.deleteEdges {s(u, v)}).Reachable v u := by
    intro x hx
    induction hx with
    | refl => exact Or.inl (Reachable.refl _)
    | @tail b c _ hxy ih =>
      rcases ih with ih | ih
      · by_cases he : s(b, c) = s(u, v)
        · rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inr (h1 ▸ ih)
          · rw [h1, h2] at hxy
            exact absurd hxy ((hO.2 _ _ (hO.1 _ _ huv)).mp huv)
        · refine Or.inl (ih.trans (Adj.reachable ?_))
          rw [deleteEdges_adj]
          exact ⟨hO.1 _ _ hxy, by simpa using he⟩
      · exact Or.inr ih
  rcases key u hR with h | h <;> exact hb h.symm

theorem OMA.solution : OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_variants_large_n_R1_H2_R1.H2 := by
  intro n W _ _ D hcard hD
  obtain ⟨T, hT, hO⟩ := hD
  classical
  have hac : ∀ u v, D.Adj u v → ¬ Relation.ReflTransGen D.Adj v u :=
    fun u v h => OMA.sumner_acyc D T hT.IsAcyclic hO u v h
  have hirr : ∀ u v, D.Adj u v → u ≠ v :=
    fun u v h e => hac u v h (e ▸ Relation.ReflTransGen.refl)
  haveI : IsPartialOrder W (Relation.ReflTransGen D.Adj) :=
    { refl := fun _ => Relation.ReflTransGen.refl
      trans := fun _ _ _ => Relation.ReflTransGen.trans
      antisymm := by
        intro a b hab hba
        by_contra hne
        rcases Relation.ReflTransGen.cases_head hab with h | ⟨c, hac', hcb⟩
        · exact hne h
        · exact hac a c hac' (hcb.trans hba) }
  obtain ⟨s, hs, hle⟩ := extend_partialOrder (Relation.ReflTransGen D.Adj)
  have hlt : ∀ a b, s a b → a ≠ b →
      (Finset.univ.filter (fun u => s u a ∧ u ≠ a)).card <
        (Finset.univ.filter (fun u => s u b ∧ u ≠ b)).card := by
    intro a b hab hne
    apply Finset.card_lt_card
    refine ⟨?_, ?_⟩
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      refine ⟨hs.trans _ _ _ hu.1 hab, ?_⟩
      rintro rfl
      exact hu.2 (hs.antisymm _ _ hu.1 hab)
    · intro hsup
      have := hsup (show a ∈ Finset.univ.filter (fun u => s u b ∧ u ≠ b) by simp [hab, hne])
      simp at this
  refine ⟨fun w => (Finset.univ.filter (fun u => s u w ∧ u ≠ w)).card, ?_, ?_, ?_⟩
  · intro a b hab
    by_contra hne
    rcases hs.total a b with h | h
    · exact absurd hab (hlt a b h hne).ne
    · exact absurd hab (hlt b a h (Ne.symm hne)).ne'
  · intro w
    rw [← hcard]
    apply Finset.card_lt_univ_of_notMem (x := w)
    simp
  · intro u v huv
    exact hlt u v (hle _ _ (Relation.ReflTransGen.single huv)) (hirr u v huv)
