import OMAReductions.R_opg_behzads_conjecture_R1
import Mathlib

/-! König's edge-colouring theorem for regular bipartite graphs: a `d`-regular bipartite graph
has a proper edge colouring with `d` colours. A `d`-regular graph with `d > 0` satisfies Hall's
condition (double counting), so Hall's theorem gives a perfect matching; deleting it leaves a
`(d-1)`-regular bipartite graph, coloured by induction, and the matching gets the last colour. -/

open SimpleGraph Finset

namespace KonigRegular

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Hall's condition for a regular graph of positive degree. -/
lemma hall (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : 0 < d)
    (hr : G.IsRegularOfDegree d) (A : Set V) :
    A.ncard ≤ (⋃ x ∈ A, G.neighborSet x).ncard := by
  classical
  obtain ⟨A, rfl⟩ : ∃ A' : Finset V, (A' : Set V) = A := ⟨A.toFinset, by simp⟩
  have hU : (⋃ x ∈ (A : Set V), G.neighborSet x) = ↑(A.biUnion fun x => G.neighborFinset x) := by
    ext y; simp
  rw [hU, Set.ncard_coe_finset, Set.ncard_coe_finset]
  have key := Finset.card_mul_le_card_mul (r := G.Adj) (s := A) (t := A.biUnion fun x => G.neighborFinset x)
    (m := d) (n := d) (fun a ha => ?_) (fun b _ => ?_)
  · exact Nat.le_of_mul_le_mul_right key hd
  · have e : (A.biUnion fun x => G.neighborFinset x).bipartiteAbove G.Adj a = G.neighborFinset a := by
      ext y
      simp only [Finset.bipartiteAbove, Finset.mem_filter, Finset.mem_biUnion, mem_neighborFinset]
      exact ⟨fun h => h.2, fun h => ⟨⟨a, ha, h⟩, h⟩⟩
    rw [e, card_neighborFinset_eq_degree, hr a]
  · rw [← hr b, ← card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.bipartiteBelow, Finset.mem_filter] at hx
    simpa [mem_neighborFinset] using hx.2.symm

/-- Two edges of a matching that share a vertex are equal. -/
lemma matching_eq {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsMatching) {e f : Sym2 V}
    (he : e ∈ M.edgeSet) (hf : f ∈ M.edgeSet) {v : V} (hve : v ∈ e) (hvf : v ∈ f) : e = f := by
  rw [← Sym2.other_spec hve] at he ⊢
  rw [← Sym2.other_spec hvf] at hf ⊢
  rw [Subgraph.mem_edgeSet] at he hf
  obtain ⟨w, _, hw⟩ := hM (M.edge_vert he)
  rw [hw _ he, hw _ hf]

theorem konig : ∀ (d : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj], G.IsRegularOfDegree d →
    G.IsBipartite → ∃ ce : G.edgeSet → Fin d, ∀ e f : G.edgeSet, e ≠ f →
      (∃ v : V, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)) → ce e ≠ ce f := by
  intro d
  induction d with
  | zero =>
    intro G _ hr _
    have empty : ∀ e : G.edgeSet, False := by
      rintro ⟨z, hz⟩
      induction z using Sym2.ind with
      | h u v =>
        rw [mem_edgeSet] at hz
        have h0 := hr u
        rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero] at h0
        have hv : v ∈ G.neighborFinset u := (mem_neighborFinset _ _ _).2 hz
        simp_all
    exact ⟨fun e => (empty e).elim, fun e => (empty e).elim⟩
  | succ d ih =>
    intro G _ hr hb
    classical
    obtain ⟨s, t, hst⟩ := hb.exists_isBipartiteWith
    obtain ⟨M, hM⟩ := exists_isPerfectMatching_of_forall_ncard_le hst (hall G d.succ_pos hr)
    let G' := G.deleteEdges M.edgeSet
    have adj' : ∀ u v, G'.Adj u v ↔ G.Adj u v ∧ ¬ M.Adj u v := by
      intro u v; simp [G', deleteEdges_adj, Subgraph.mem_edgeSet]
    have hr' : G'.IsRegularOfDegree d := by
      intro v
      obtain ⟨w, hw, hu⟩ := hM.1 (hM.2 v)
      have e : G'.neighborFinset v = (G.neighborFinset v).erase w := by
        ext x
        simp only [mem_neighborFinset, Finset.mem_erase, adj']
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨fun h => h2 (h ▸ hw), h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, fun h => h1 (hu x h)⟩
      rw [← card_neighborFinset_eq_degree, e,
        Finset.card_erase_of_mem ((mem_neighborFinset _ _ _).2 (M.adj_sub hw)),
        card_neighborFinset_eq_degree, hr v]
      rfl
    obtain ⟨ce', hce'⟩ := ih G' hr' (hb.mono_left (deleteEdges_le _))
    have mem' : ∀ e : G.edgeSet, (e : Sym2 V) ∉ M.edgeSet → (e : Sym2 V) ∈ G'.edgeSet := by
      intro e he; rw [edgeSet_deleteEdges]; exact ⟨e.2, he⟩
    refine ⟨fun e => if h : (e : Sym2 V) ∈ M.edgeSet then Fin.last d
      else Fin.castSucc (ce' ⟨e, mem' e h⟩), ?_⟩
    rintro e f hne ⟨v, hve, hvf⟩
    by_cases he : (e : Sym2 V) ∈ M.edgeSet <;> by_cases hf : (f : Sym2 V) ∈ M.edgeSet <;>
      simp only [he, hf, dite_true, dite_false]
    · exact absurd (Subtype.ext (matching_eq hM.1 he hf hve hvf)) hne
    · exact (Fin.castSucc_lt_last _).ne'
    · exact (Fin.castSucc_lt_last _).ne
    · intro h
      exact hce' ⟨e, mem' e he⟩ ⟨f, mem' f hf⟩
        (fun h' => hne (Subtype.ext (by simpa using congrArg Subtype.val h'))) ⟨v, hve, hvf⟩
        (Fin.castSucc_injective _ h)

end KonigRegular

theorem OMA.solution : OMA.R_opg_behzads_conjecture_R1.H1 := by
  intro V _ _ G _ d hr hb
  classical
  exact KonigRegular.konig d G hr hb
