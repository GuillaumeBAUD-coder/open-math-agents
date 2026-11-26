import FormalConjectures.ErdosProblems.«23»

/-! # Bipartizing a triangle-free graph on five vertices -/
-- Credit: @steveDOTdigital

open SimpleGraph Finset

namespace OMA.FiveVertices

private theorem matching_bipartite (G : SimpleGraph (Fin 5))
    (unique : ∀ v x y, G.Adj v x → G.Adj v y → x = y) : G.IsBipartite := by
  classical
  let c (x : Fin 5) : Fin 2 := if ∃ z < x, G.Adj x z then 1 else 0
  have oriented {x y : Fin 5} (h : G.Adj x y) (lt : x < y) : c x ≠ c y := by
    have hy : ∃ z < y, G.Adj y z := ⟨x, lt, h.symm⟩
    have hx : ¬ ∃ z < x, G.Adj x z := by
      rintro ⟨z, hzx, hxz⟩
      exact lt.asymm ((unique x z y hxz h) ▸ hzx)
    simp [c, hx, hy]
  refine ⟨Coloring.mk c (fun {x y} h => ?_)⟩
  rcases lt_or_gt_of_ne h.ne with lt | lt
  · exact oriented h lt
  · exact (oriented h.symm lt).symm

end OMA.FiveVertices

theorem OMA.solution : type_of% @Erdos23.erdos_23.variants.n1 := by
  classical
  intro G hfree
  by_cases fork : ∃ v x y, G.Adj v x ∧ G.Adj v y ∧ x ≠ y
  · obtain ⟨v, x, y, hvx, hvy, hxy⟩ := fork
    -- The neighbors of v are independent. A same-color edge can use only
    -- the two vertices outside {v,x,y}.
    let c (z : Fin 5) : Fin 2 := if G.Adj v z then 1 else 0
    let H := G ⊓ (⊤ : SimpleGraph (Fin 2)).comap c
    let R : Finset (Fin 5) := ({v,x,y} : Finset (Fin 5))ᶜ
    have hR : R.card = 2 := by simp [R, card_compl, hvx.ne, hvy.ne, hxy]
    refine ⟨H, inf_le_left, ⟨Coloring.mk c (fun h => h.2)⟩, ?_⟩
    have endpoints {u w : Fin 5} (huw : G.Adj u w) (same : c u = c w) : u ∈ R := by
      have iff_adj : G.Adj v u ↔ G.Adj v w := by
        by_cases hu : G.Adj v u <;> by_cases hw : G.Adj v w <;> simp_all [c]
      have hu : ¬ G.Adj v u := fun h => hfree {v,u,w}
        (is3Clique_triple_iff.mpr ⟨h, iff_adj.mp h, huw⟩)
      have huv : u ≠ v := by rintro rfl; exact hu (iff_adj.mpr huw)
      have hux : u ≠ x := fun e => hu (e ▸ hvx)
      have huy : u ≠ y := fun e => hu (e ▸ hvy)
      simp [R, huv, hux, huy]
    have used {e : Sym2 (Fin 5)} (hg : e ∈ G.edgeSet) (hn : e ∉ H.edgeSet) : e.toFinset = R := by
      apply eq_of_subset_of_card_le _ (by rw [hR, G.card_toFinset_mem_edgeFinset ⟨e,mem_edgeFinset.mpr hg⟩])
      induction e using Sym2.ind with
      | _ u w =>
        have hadj : G.Adj u w := hg
        have same : c u = c w := by
          by_contra ne
          exact hn (show H.Adj u w from ⟨hadj, ne⟩)
        rw [Sym2.toFinset_mk_eq]
        exact insert_subset (endpoints hadj same) (singleton_subset_iff.mpr (endpoints hadj.symm same.symm))
    refine Finset.card_le_one_iff.2 fun he hf => Sym2.ext fun z => ?_
    simp only [mem_sdiff, mem_edgeFinset] at he hf
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, used he.1 he.2, used hf.1 hf.2]
  · refine ⟨G, le_rfl, OMA.FiveVertices.matching_bipartite G ?_, by simp⟩
    intro v x y hx hy
    exact Classical.byContradiction fun h => fork ⟨v,x,y,hx,hy,h⟩
