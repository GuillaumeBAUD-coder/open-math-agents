import FormalConjectures.ErdosProblems.«23»

-- Credit: @steveDOTdigital
namespace OMA.FiveVertices

def colorOf (C : Finset (Fin 5)) (x : Fin 5) : Fin 2 :=
  if x ∈ C then 0 else 1

-- Enumerate the subsets of the ten possible edges. For triangle-free inputs
-- the certificate supplies a cut with at most one edge on the same side.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1600000 in
theorem cut_exists :
    ∀ E ∈ ((Finset.univ : Finset (Sym2 (Fin 5))).filter (fun e => ¬e.IsDiag)).powerset,
      (∀ x y z : Fin 5, s(x,y) ∈ E → s(x,z) ∈ E → s(y,z) ∉ E) →
      ∃ C ∈ (Finset.univ : Finset (Fin 5)).powerset,
        (E.filter (fun e => (e.map (colorOf C)).IsDiag)).card ≤ 1 := by
  decide +kernel

end OMA.FiveVertices

open SimpleGraph OMA.FiveVertices

theorem OMA.solution : type_of% @Erdos23.erdos_23.variants.n1 := by
  classical
  intro G hfree
  have hedges : G.edgeFinset ∈
      ((Finset.univ : Finset (Sym2 (Fin 5))).filter (fun e => ¬e.IsDiag)).powerset :=
    Finset.mem_powerset.mpr fun e he =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ e, G.not_isDiag_of_mem_edgeFinset he⟩
  obtain ⟨C, _, hcard⟩ := cut_exists G.edgeFinset hedges (by
    intro x y z hxy hxz hyz
    exact hfree {x,y,z} (is3Clique_triple_iff.mpr
      ⟨mem_edgeFinset.mp hxy, mem_edgeFinset.mp hxz, mem_edgeFinset.mp hyz⟩))
  let H := G ⊓ (⊤ : SimpleGraph (Fin 2)).comap (colorOf C)
  refine ⟨H, inf_le_left, ⟨Coloring.mk (colorOf C) (fun h => h.2)⟩, ?_⟩
  apply le_trans (Finset.card_le_card ?_) hcard
  intro e
  induction e using Sym2.ind with
  | _ x y =>
    intro he
    obtain ⟨hg, hn⟩ := Finset.mem_sdiff.mp he
    refine Finset.mem_filter.mpr ⟨hg, ?_⟩
    change colorOf C x = colorOf C y
    by_contra hne
    exact hn (mem_edgeFinset.mpr (show H.Adj x y from ⟨mem_edgeFinset.mp hg, hne⟩))
