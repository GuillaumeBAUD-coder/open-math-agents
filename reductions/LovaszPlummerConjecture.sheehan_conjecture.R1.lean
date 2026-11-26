import FormalConjectures.Wikipedia.LovaszPlummerConjecture

namespace OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1

open SimpleGraph LovaszPlummerConjecture

/-- The second-cycle conclusion of Thomason's parity argument when both
endpoints of the chosen initial edge may have even degree. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ∀ (v : V) (c : G.Walk v v), IsHamiltonianCycle G c →
      ∀ (e : Sym2 V), e ∈ c.edges →
        (∀ u, G.degree u % 2 ≠ 1 → u ∈ e) →
        ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
          c'.edges.toFinset ≠ c.edges.toFinset

open scoped Classical in
/-- The remaining cases have no matching of unused edges whose uncovered
vertices all lie on a single edge of the given Hamiltonian cycle. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ u, G.degree u = 4) →
    ∀ (v : V) (c : G.Walk v v), IsHamiltonianCycle G c →
      (¬ ∃ (M : SimpleGraph V) (e : Sym2 V),
        M ≤ G ∧ e ∈ c.edges ∧ (∀ u, M.degree u ≤ 1) ∧
          (∀ u, M.degree u = 0 → u ∈ e) ∧ (∀ f ∈ c.edges, f ∉ M.edgeSet)) →
      ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
        c'.edges.toFinset ≠ c.edges.toFinset

theorem main : H1 → H2 → type_of% @LovaszPlummerConjecture.sheehan_conjecture := by
  intro parity remaining V _ _ G _ hFour v c hc
  classical
  by_cases hm : ∃ (M : SimpleGraph V) (e : Sym2 V),
      M ≤ G ∧ e ∈ c.edges ∧ (∀ u, M.degree u ≤ 1) ∧
        (∀ u, M.degree u = 0 → u ∈ e) ∧ (∀ f ∈ c.edges, f ∉ M.edgeSet)
  · obtain ⟨M, e, hMG, he, hMatching, hUncovered, hAvoid⟩ := hm
    let H := G \ M
    have hHG : H ≤ G := sdiff_le
    have hDegree (u : V) : H.degree u = G.degree u - M.degree u := by
      have hSubset : M.neighborFinset u ⊆ G.neighborFinset u := by
        intro x hx
        exact (mem_neighborFinset _ _ _).2 (hMG ((mem_neighborFinset _ _ _).1 hx))
      change ((G \ M).neighborFinset u).card =
        (G.neighborFinset u).card - (M.neighborFinset u).card
      rw [neighborFinset_sdiff, Finset.card_sdiff_of_subset hSubset]
    have hEdges : ∀ f, f ∈ c.edges → f ∈ H.edgeSet := by
      intro f hf
      change f ∈ (G \ M).edgeSet
      rw [edgeSet_sdiff]
      exact ⟨c.edges_subset_edgeSet hf, hAvoid f hf⟩
    let cH := c.transfer H hEdges
    have hcH : IsHamiltonianCycle H cH :=
      ⟨hc.1.transfer hEdges, fun u => by simpa [cH] using hc.2 u⟩
    have hExceptional (u : V) (hu : H.degree u % 2 ≠ 1) : u ∈ e := by
      apply hUncovered u
      by_contra hNotZero
      have hOne : M.degree u = 1 := by
        have hAtMostOne := hMatching u
        omega
      apply hu
      rw [hDegree u, hFour u, hOne]
    obtain ⟨w, d, hd, hDistinct⟩ :=
      parity H v cH hcH e (by simpa [cH] using he) hExceptional
    have hDEdges : ∀ f, f ∈ d.edges → f ∈ G.edgeSet := by
      intro f hf
      exact edgeSet_mono hHG (d.edges_subset_edgeSet hf)
    refine ⟨w, d.transfer G hDEdges, ⟨hd.1.transfer hDEdges, ?_⟩, ?_⟩
    · intro u
      simpa using hd.2 u
    · intro hEqual
      apply hDistinct
      simpa [cH] using hEqual
  · exact remaining G hFour v c hc hm

end OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1
