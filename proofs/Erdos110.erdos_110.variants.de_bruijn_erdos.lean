import FormalConjectures.ErdosProblems.«110»

-- Problem: Erdős Problem 110 — de bruijn erdos
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/110.lean:89 (declaration Erdos110.erdos_110.variants.de_bruijn_erdos)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open SimpleGraph

namespace OMA

/-- Colorability passes to smaller subgraphs. -/
lemma colorable_of_le {V : Type*} {G : SimpleGraph V} {x y : G.Subgraph} (h : x ≤ y) {k : ℕ}
    (hy : y.coe.Colorable k) : x.coe.Colorable k := by
  obtain ⟨c⟩ := hy
  exact ⟨c.comp (Subgraph.inclusion h)⟩

end OMA

theorem OMA.solution : type_of% @Erdos110.erdos_110.variants.de_bruijn_erdos := by
  intro V G hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  classical
  let I : Finset V → G.Subgraph := fun s => (⊤ : G.Subgraph).induce (s : Set V)
  let P : ℕ → Prop := fun k => ∃ s : Finset V, s.card = k ∧ ¬ (I s).coe.Colorable m
  have hG' : ¬ G.Colorable m := by
    intro h
    have := h.chromaticNumber_le
    rw [hG] at this
    exact absurd this (by simp)
  have hex : ∃ k, P k := by
    by_contra hcon
    push_neg at hcon
    apply hG'
    apply nonempty_hom_of_forall_finite_subgraph_hom
    intro G' hfin
    have hs : ((hfin.toFinset : Finset V) : Set V) = G'.verts := hfin.coe_toFinset
    have hle : G' ≤ I hfin.toFinset := by
      show G' ≤ (⊤ : G.Subgraph).induce ((hfin.toFinset : Finset V) : Set V)
      rw [hs]
      exact Subgraph.le_induce_top_verts
    have hcol : (I hfin.toFinset).coe.Colorable m := by
      by_contra hc
      exact hcon _ ⟨_, rfl, hc⟩
    exact (OMA.colorable_of_le hle hcol).some
  obtain ⟨s, hscard, hs⟩ := Nat.find_spec hex
  have hmin : ∀ t : Finset V, t.card < s.card → (I t).coe.Colorable m := by
    intro t ht
    by_contra hc
    exact Nat.find_min hex (hscard ▸ ht) ⟨t, rfl, hc⟩
  refine ⟨I s, by simp [I], le_antisymm ?_ ?_⟩
  · -- `m + 1` colors suffice
    have hne : s.Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty] at he
      apply hs
      subst he
      haveI : IsEmpty (I ∅).verts := by
        refine ⟨fun x => ?_⟩
        have := x.2
        simp [I] at this
      exact Colorable.of_isEmpty m
    obtain ⟨v, hv⟩ := hne
    have hlt : (s.erase v).card < s.card := Finset.card_erase_lt_of_mem hv
    obtain ⟨c⟩ := hmin _ hlt
    have hverts : ∀ w : (I s).verts, (w : V) ≠ v → (w : V) ∈ (I (s.erase v)).verts := by
      intro w hw
      have := w.2
      simp only [I, Subgraph.induce_verts, Finset.mem_coe] at this ⊢
      exact Finset.mem_erase.mpr ⟨hw, this⟩
    let f : (I s).verts → Fin (m + 1) := fun w =>
      if h : (w : V) = v then Fin.last m else Fin.castSucc (c ⟨w, hverts w h⟩)
    have hcol : (I s).coe.Colorable (m + 1) := by
      refine ⟨Coloring.mk f ?_⟩
      intro a b hab
      have hab' : (I s).Adj a b := hab
      simp only [I, Subgraph.induce_adj, Subgraph.top_adj] at hab'
      simp only [f]
      by_cases ha : (a : V) = v
      · by_cases hb : (b : V) = v
        · exact absurd (ha.trans hb.symm) (G.ne_of_adj hab'.2.2)
        · rw [dif_pos ha, dif_neg hb]
          exact (Fin.castSucc_lt_last _).ne'
      · by_cases hb : (b : V) = v
        · rw [dif_neg ha, dif_pos hb]
          exact (Fin.castSucc_lt_last _).ne
        · rw [dif_neg ha, dif_neg hb]
          intro he
          have hadj : (I (s.erase v)).coe.Adj ⟨a, hverts a ha⟩ ⟨b, hverts b hb⟩ := by
            show (I (s.erase v)).Adj a b
            simp only [I, Subgraph.induce_adj, Subgraph.top_adj, Finset.coe_erase,
              Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe]
            exact ⟨⟨hab'.1, ha⟩, ⟨hab'.2.1, hb⟩, hab'.2.2⟩
          exact c.valid hadj (Fin.castSucc_injective _ he)
    exact_mod_cast hcol.chromaticNumber_le
  · -- not `m`-colorable
    have h1 : ((m : ℕ) : ℕ∞) < (I s).coe.chromaticNumber :=
      lt_chromaticNumber_iff_not_colorable.mpr hs
    exact_mod_cast Order.add_one_le_of_lt h1
