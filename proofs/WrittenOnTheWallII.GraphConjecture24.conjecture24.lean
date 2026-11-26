import FormalConjectures.WrittenOnTheWallII.GraphConjecture24

/-! In the rook graph on an eight-by-eight board, every induced bipartite graph
has at most sixteen vertices, while each square has forty-nine squares at distance two. -/

open SimpleGraph

universe u

namespace OMA.Rook

abbrev Axis := ULift.{u} (Fin 8)
abbrev Board := Axis.{u} × Axis.{u}

def graph : SimpleGraph Board.{u} where
  Adj v w := v ≠ w ∧ (v.1 = w.1 ∨ v.2 = w.2)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.imp Eq.symm Eq.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma cross {v w : Board.{u}} (h₁ : v.1 ≠ w.1) (h₂ : v.2 ≠ w.2) :
    graph.Adj v (v.1,w.2) ∧ graph.Adj w (v.1,w.2) := by
  exact ⟨⟨fun h => by
      have hh := congrArg Prod.snd h
      exact h₂ hh, Or.inl rfl⟩,
    ⟨fun h => by
      have hh := congrArg Prod.fst h
      exact h₁ hh.symm, Or.inr rfl⟩⟩

lemma connected : graph.{u}.Connected := by
  constructor
  intro v w
  by_cases he : v = w
  · exact he ▸ Reachable.refl _
  by_cases hr : v.1 = w.1
  · exact (show graph.Adj v w from ⟨he, Or.inl hr⟩).reachable
  by_cases hc : v.2 = w.2
  · exact (show graph.Adj v w from ⟨he, Or.inr hc⟩).reachable
  obtain ⟨hv, hw⟩ := cross hr hc
  exact hv.reachable.trans hw.reachable.symm

lemma distance_two {v w : Board.{u}} (hr : v.1 ≠ w.1) (hc : v.2 ≠ w.2) :
    graph.dist v w = 2 := by
  have h : graph.edist v w = 2 := edist_eq_two_iff.mpr
    ⟨fun h => hr (congrArg Prod.fst h), fun h => h.2.elim hr hc,
      (v.1,w.2), cross hr hc⟩
  simp [SimpleGraph.dist, h]

lemma even_bound (v : Board.{u}) : 49 ≤ distEven graph v := by
  classical
  let other := (Finset.univ.erase v.1) ×ˢ (Finset.univ.erase v.2)
  have hs : other ⊆ Finset.univ.filter (fun w : Board => Even (graph.dist v w)) := by
    intro w hw
    obtain ⟨hr, hc⟩ := Finset.mem_product.mp hw
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [distance_two (Ne.symm (Finset.mem_erase.mp hr).1) (Ne.symm (Finset.mem_erase.mp hc).1)]
    decide
  have hcard : other.card = 49 := by simp [other, Axis]
  exact hcard ▸ Finset.card_le_card hs

lemma min_bound :
    49 ≤ (Finset.univ.image (distEven graph.{u})).min' (by simp) := by
  apply Finset.le_min'
  intro k hk
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hk
  exact even_bound v

lemma bip_bound : b graph.{u} ≤ 16 := by
  unfold b
  have bound : graph.{u}.largestInducedBipartiteSubgraphSize ≤ 16 := by
    unfold largestInducedBipartiteSubgraphSize
    apply csSup_le
    · refine ⟨0, ∅, ?_, rfl⟩
      rw [induce_isBipartite_iff_exists_coloring]
      exact ⟨fun _ => 0, by simp⟩
    · rintro k ⟨s, hs, rfl⟩
      obtain ⟨color, valid⟩ := (induce_isBipartite_iff_exists_coloring _ _).mp hs
      let f : s → Axis × Fin 2 := fun v => (v.val.1, color v.val)
      have inj : Function.Injective f := by
        intro v w h
        apply Subtype.ext
        by_contra hne
        have hr := congrArg Prod.fst h
        have hc := congrArg Prod.snd h
        exact valid _ v.property _ w.property (show graph.Adj _ _ from ⟨hne, Or.inl hr⟩)
          hc
      simpa [Axis] using Fintype.card_le_of_injective f inj
  exact_mod_cast bound

end OMA.Rook

open OMA.Rook

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture24.conjecture24 := by
  intro allGraphs
  have h := allGraphs graph connected
  dsimp only at h
  have hm : (49 : ℝ) ≤ ((Finset.univ.image (distEven graph)).min' (by simp) : ℕ) := by
    exact_mod_cast min_bound
  have hc := Int.le_ceil ((((Finset.univ.image (distEven graph)).min' (by simp) : ℕ) : ℝ) / 3)
  have hn : (0 : ℝ) ≤ ((Finset.univ.image (fun v => indepNeighborsCard graph v)).max' (by simp) : ℕ) := by positivity
  linarith [bip_bound]
