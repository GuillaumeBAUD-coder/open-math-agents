import FormalConjectures.Wikipedia.TotalColoringConjecture
import Mathlib

/-! Molloy and Reed, A Bound on the Total Chromatic Number (1998).
Separate the high-degree estimate on regular graphs, regular completion,
and the elementary greedy estimate needed for bounded degrees. -/
open SimpleGraph
namespace OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_molloy_reed_R1

/-- The uniform additive bound for regular graphs of sufficiently high degree. -/
def H1 : Prop := ∃ (C D : ℕ), ∀ {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ),
  D ≤ d → G.IsRegularOfDegree d → G.totalChromaticNumber ≤ d+C

/-- Every finite graph embeds as an induced subgraph of a finite regular
graph of degree equal to its maximum degree. -/
def H2 : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj],
  ∃ W : Type, ∃ _ : Fintype W, ∃ _ : DecidableEq W, ∃ K : SimpleGraph W,
    ∃ _ : DecidableRel K.Adj, Nonempty (G ↪g K) ∧ K.IsRegularOfDegree G.maxDegree

/-- A greedy coloring of the total graph has at most twice the maximum degree plus one colors. -/
def H3 : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj],
  G.totalChromaticNumber ≤ 2*G.maxDegree+1

theorem totalChromatic_restrict {V W : Type} [Fintype W]
    {G : SimpleGraph V} {K : SimpleGraph W} [DecidableRel K.Adj]
    (f : G ↪g K) : G.totalChromaticNumber ≤ K.totalChromaticNumber := by
  have hK : K.TotalColorable K.totalChromaticNumber := by
    change sInf {n | K.TotalColorable n} ∈ {n | K.TotalColorable n}
    exact Nat.sInf_mem ⟨_,K.totalColorable_card_add_card⟩
  obtain ⟨c,hc⟩ := hK
  have mem_edge {v : V} {e : G.edgeSet} (hv : v ∈ (e : Sym2 V)) :
      f v ∈ (f.mapEdgeSet e : Sym2 W) :=
    Sym2.mem_map.mpr ⟨v,hv,rfl⟩
  apply Nat.sInf_le
  show G.TotalColorable K.totalChromaticNumber
  refine ⟨fun x ↦ c (Sum.map f f.mapEdgeSet x),?_,?_,?_⟩
  · intro u v hadj
    exact hc.1 (f u) (f v) (f.map_adj_iff.mpr hadj)
  · intro a b hne hm
    obtain ⟨v,ha,hb⟩ := hm
    exact hc.2.1 (f.mapEdgeSet a) (f.mapEdgeSet b)
      (fun he ↦ hne (f.mapEdgeSet.injective he)) ⟨f v,mem_edge ha,mem_edge hb⟩
  · intro v e hv
    exact hc.2.2 (f v) (f.mapEdgeSet e) (mem_edge hv)

theorem main : H1 → H2 → H3 → type_of% @TotalColoringConjecture.total_coloring_conjecture.variants.molloy_reed := by
  intro hregular hcompletion hgreedy
  obtain ⟨C,D,h⟩ := hregular
  refine ⟨C+D+1,?_⟩
  intro V _ _ G _
  by_cases hd : D ≤ G.maxDegree
  · obtain ⟨W,wf,wd,K,kd,⟨f⟩,hk⟩ := hcompletion G
    have bound := (totalChromatic_restrict f).trans (h K G.maxDegree hd hk)
    omega
  · have bound := hgreedy G
    omega

end OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_molloy_reed_R1
