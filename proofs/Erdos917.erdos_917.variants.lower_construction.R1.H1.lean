import OMAReductions.R_Erdos917_erdos_917_variants_lower_construction_R1
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open SimpleGraph

namespace OMA.OddCycle

-- Cut at the missing edge and alternate colors starting at its successor.
lemma cutColorable (n : ℕ) (a : Fin (n + 3)) :
    ((cycleGraph (n + 3)).deleteEdges ({s(a, a + 1)} : Set _)).Colorable 2 := by
  let color (x : Fin (n + 3)) : Fin 2 :=
    ⟨(x - (a + 1)).val % 2, Nat.mod_lt _ (by decide)⟩
  have consecutive (x : Fin (n + 3)) (hx : x ≠ a) : color x ≠ color (x + 1) := by
    have hlast : x - (a + 1) ≠ Fin.last (n + 2) := by
      intro h
      apply hx
      apply sub_eq_zero.mp
      calc
        x - a = (x - (a + 1)) + 1 := by abel
        _ = 0 := by rw [h, Fin.last_add_one]
    intro heq
    have hval := congrArg Fin.val heq
    change (x - (a + 1)).val % 2 = (x + 1 - (a + 1)).val % 2 at hval
    rw [show x + 1 - (a + 1) = (x - (a + 1)) + 1 by abel,
      Fin.val_add_one, if_neg hlast] at hval
    omega
  refine ⟨Coloring.mk color ?_⟩
  intro x y h
  obtain ⟨adj, miss⟩ := deleteEdges_adj.mp h
  rcases cycleGraph_adj.mp adj with h | h
  · have hxy : x = y + 1 := sub_eq_iff_eq_add'.mp h
    subst x
    apply Ne.symm (consecutive y ?_)
    rintro rfl
    exact miss (Set.mem_singleton_iff.mpr Sym2.eq_swap)
  · have hyx : y = x + 1 := sub_eq_iff_eq_add'.mp h
    subst y
    apply consecutive x
    rintro rfl
    exact miss rfl

lemma deleteEdgeColorable (n : ℕ) (e : Sym2 (Fin (n + 3)))
    (he : e ∈ (cycleGraph (n + 3)).edgeSet) :
    ((cycleGraph (n + 3)).deleteEdges ({e} : Set _)).Colorable 2 := by
  induction e using Sym2.inductionOn with
  | _ x y =>
    rcases cycleGraph_adj.mp he with h | h
    · have hxy : x = y + 1 := sub_eq_iff_eq_add'.mp h
      subst x
      rw [Sym2.eq_swap (a := y + 1) (b := y)]
      exact cutColorable n y
    · have hyx : y = x + 1 := sub_eq_iff_eq_add'.mp h
      subst y
      exact cutColorable n x

lemma edgeCritical (n : ℕ) (hodd : Odd (n + 3)) (e : Sym2 (Fin (n + 3)))
    (he : e ∈ (cycleGraph (n + 3)).edgeSet) :
    (cycleGraph (n + 3)).IsCriticalEdge e := by
  unfold IsCriticalEdge IsCriticalEdges
  rw [chromaticNumber_cycleGraph_of_odd _ (by omega) hodd]
  exact lt_of_le_of_lt (deleteEdgeColorable n e he).chromaticNumber_le (by decide)

-- Deleting a vertex also removes any edge incident to it.
lemma vertexDeletionLeIncidentEdgeDeletion {V : Type*} (G : SimpleGraph V) (v w : V) :
    ((⊤ : G.Subgraph).deleteVerts {v}).coe.chromaticNumber ≤
      (G.deleteEdges {s(v, w)}).chromaticNumber := by
  apply chromaticNumber_mono_of_hom
  refine { toFun := Subtype.val, map_rel' := ?_ }
  intro a b hab
  refine deleteEdges_adj.mpr ⟨((⊤ : G.Subgraph).deleteVerts {v}).adj_sub hab, ?_⟩
  intro he
  rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp he) with h | h
  · exact a.property.2 h.1
  · exact b.property.2 h.2

lemma cycleVertexCriticalOfEdgeCritical {n : ℕ} (hn : 3 ≤ n)
    (hedge : ∀ e ∈ (cycleGraph n).edgeSet, (cycleGraph n).IsCriticalEdge e) :
    ∀ v, (⊤ : (cycleGraph n).Subgraph).IsCriticalVertex v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
  intro v
  unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts
  rw [chromaticNumber_congr Subgraph.topIso]
  let w := v + 1
  have hadj : (cycleGraph (2 + k)).Adj v w := by
    rw [cycleGraph_adj']
    right
    change ((v + 1 - v : Fin (2 + k))).val = 1
    simp [Nat.mod_eq_of_lt (show 1 < 2 + k by omega)]
  exact (vertexDeletionLeIncidentEdgeDeletion _ v w).trans_lt
    (hedge s(v, w) hadj)

lemma oddCycleEdgeCount (k : ℕ) : (cycleGraph (k + 3)).edgeSet.ncard = k + 3 := by
  have h := (cycleGraph (k + 3)).sum_degrees_eq_twice_card_edges
  simp only [cycleGraph_degree_three_le, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at h
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  omega

end OMA.OddCycle

theorem OMA.solution : OMA.R_Erdos917_erdos_917_variants_lower_construction_R1.H1 := by
  intro b hodd hb
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 3 := ⟨b - 3, by omega⟩
  have hχ := chromaticNumber_cycleGraph_of_odd (k + 3) (by omega) hodd
  have hedge := OMA.OddCycle.edgeCritical k hodd
  exact ⟨cycleGraph (k + 3), ⟨⟨hχ, OMA.OddCycle.cycleVertexCriticalOfEdgeCritical (by omega) hedge⟩,
    hedge⟩, OMA.OddCycle.oddCycleEdgeCount k⟩
