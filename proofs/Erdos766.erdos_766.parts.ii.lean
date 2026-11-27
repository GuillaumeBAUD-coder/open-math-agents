import FormalConjectures.ErdosProblems.«766»

/-
Problem: Erdős Problem 766, part ii
Upstream: formal-conjectures FormalConjectures/ErdosProblems/766.lean
(declaration Erdos766.erdos_766.parts.ii)

Written with Claude Code (AI-assisted).

Scope note. This proves the statement exactly as formalized, which is about
Erdős's 1964 function f_1(n;k,l) (Erdos766.forcingNumber): the least m such
that every graph with n vertices and m edges contains SOME graph with k
vertices and l edges. It does not address the version on erdosproblems.com,
which is about the minimum of ex(n;G) over graphs G with k vertices and l
edges (Erdos766.erdos_766.variants.minExtremalNumber_strictMonoOn).

Argument. Let l < l', l <= C(k,2), k <= n, and m' = f_1(n;k,l').
* m' >= 1, because the empty graph contains no graph with l' >= 1 edges.
* Every graph G with m' - 1 edges contains a graph with k vertices and l
  edges, hence f_1(n;k,l) <= m' - 1 < m':
  - if G is complete, it contains every graph on k <= n vertices, and there
    is one with exactly l <= C(k,2) edges;
  - otherwise add a missing edge e to get G' with m' edges. G' contains some
    H' with k vertices and l' edges through an injective map f. At most one
    edge of H' is mapped to e, so at least l' - 1 >= l edges of H' are mapped
    into G; any l of them form the required graph.
So f_1(n;k,.) is strictly increasing on [0, C(k,2)] for every n >= k, and
floor(k^2/4) <= C(k,2) whenever the interval (k, floor(k^2/4)] is nonempty.
-/

namespace Erdos766Aux

open Erdos766
open scoped SimpleGraph

/-- A graph with at least `l` edges has a subgraph with exactly `l` edges. -/
theorem exists_le_edge_ncard {k l : ℕ} (K : SimpleGraph (Fin k))
    (h : l ≤ K.edgeSet.ncard) :
    ∃ H : SimpleGraph (Fin k), H ≤ K ∧ H.edgeSet.ncard = l := by
  obtain ⟨s, hs, hcard⟩ := Set.exists_subset_card_eq h
  refine ⟨SimpleGraph.fromEdgeSet s, ?_, ?_⟩
  · intro a b hab
    rw [SimpleGraph.fromEdgeSet_adj] at hab
    exact hs hab.1
  · have hE : (SimpleGraph.fromEdgeSet s).edgeSet = s := by
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      ext e
      constructor
      · intro he
        exact he.1
      · intro he
        exact ⟨he, K.not_isDiag_of_mem_edgeSet (hs he)⟩
    rw [hE, hcard]

theorem edge_ncard_le (n : ℕ) (G : SimpleGraph (Fin n)) :
    G.edgeSet.ncard ≤ n.choose 2 := by
  classical
  have h := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G)
  rw [Fintype.card_fin, ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] at h
  exact h

theorem top_edge_ncard (k : ℕ) :
    (⊤ : SimpleGraph (Fin k)).edgeSet.ncard = k.choose 2 := by
  classical
  have h := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin k)
  rw [Fintype.card_fin, ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] at h
  exact h

theorem forcingNumber_lt {n k l l' : ℕ} (hkn : k ≤ n) (hl : l ≤ k.choose 2)
    (hll : l < l') : forcingNumber n k l < forcingNumber n k l' := by
  classical
  have hne : {m : ℕ | ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
      ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l' ∧ H ⊑ G}.Nonempty := by
    refine ⟨n.choose 2 + 1, ?_⟩
    intro G hG
    have := edge_ncard_le n G
    omega
  have hmem : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = forcingNumber n k l' →
      ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l' ∧ H ⊑ G := Nat.sInf_mem hne
  -- the forcing number for `l'` is positive
  have hpos : 0 < forcingNumber n k l' := by
    rcases Nat.eq_zero_or_pos (forcingNumber n k l') with h0 | h
    · exfalso
      obtain ⟨H, hH, ⟨f⟩⟩ := hmem ⊥ (by rw [h0]; simp)
      have hne' : H.edgeSet.Nonempty := by
        apply Set.nonempty_of_ncard_ne_zero
        omega
      obtain ⟨e, he⟩ := hne'
      induction e using Sym2.ind with
      | _ x y =>
        have hxy : H.Adj x y := he
        exact f.toHom.map_adj hxy
    · exact h
  -- every graph with one edge less contains a graph with `l` edges
  have hkey : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = forcingNumber n k l' - 1 →
      ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G := by
    intro G hG
    by_cases hGtop : G = ⊤
    · obtain ⟨H, -, hH⟩ := exists_le_edge_ncard (⊤ : SimpleGraph (Fin k))
        (le_of_le_of_eq hl (top_edge_ncard k).symm)
      refine ⟨H, hH, ⟨⟨⟨Fin.castLE hkn, ?_⟩, Fin.castLE_injective hkn⟩⟩⟩
      intro x y hxy
      rw [hGtop, SimpleGraph.top_adj]
      intro hc
      exact hxy.ne (Fin.castLE_injective hkn hc)
    · have hex : ∃ a b : Fin n, a ≠ b ∧ ¬ G.Adj a b := by
        by_contra hcon
        apply hGtop
        ext x y
        rw [SimpleGraph.top_adj]
        constructor
        · intro hxy
          exact hxy.ne
        · intro hxy
          by_contra hna
          exact hcon ⟨x, y, hxy, hna⟩
      obtain ⟨a, b, hab, hnadj⟩ := hex
      have hnotmem : s(a, b) ∉ G.edgeSet := hnadj
      have hE : (SimpleGraph.fromEdgeSet (insert s(a, b) G.edgeSet)).edgeSet =
          insert s(a, b) G.edgeSet := by
        rw [SimpleGraph.edgeSet_fromEdgeSet]
        ext e
        constructor
        · intro he
          exact he.1
        · intro he
          refine ⟨he, ?_⟩
          rcases he with he | he
          · rw [he]
            exact fun hd => hab (Sym2.mk_isDiag_iff.1 hd)
          · exact G.not_isDiag_of_mem_edgeSet he
      have hcard : (SimpleGraph.fromEdgeSet (insert s(a, b) G.edgeSet)).edgeSet.ncard =
          forcingNumber n k l' := by
        rw [hE, Set.ncard_insert_of_notMem hnotmem (Set.toFinite _), hG]
        omega
      obtain ⟨H', hH', ⟨f⟩⟩ := hmem _ hcard
      have hsub : H'.edgeSet ⊆ (H' ⊓ G.comap (fun x => f x)).edgeSet ∪
          {e | Sym2.map (fun x => f x) e = s(a, b)} := by
        intro e he
        induction e using Sym2.ind with
        | _ x y =>
          have hxy : H'.Adj x y := he
          have hadj := f.toHom.map_adj hxy
          rw [SimpleGraph.fromEdgeSet_adj] at hadj
          rcases hadj.1 with h1 | h1
          · right
            exact h1
          · left
            exact ⟨hxy, h1⟩
      have hT : ({e | Sym2.map (fun x => f x) e = s(a, b)} : Set (Sym2 (Fin k))).ncard ≤ 1 := by
        apply (Set.ncard_le_one (Set.toFinite _)).2
        intro e1 he1 e2 he2
        exact Sym2.map.injective f.injective (he1.trans he2.symm)
      have h1 : H'.edgeSet.ncard ≤ ((H' ⊓ G.comap (fun x => f x)).edgeSet ∪
          {e | Sym2.map (fun x => f x) e = s(a, b)}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 := Set.ncard_union_le (H' ⊓ G.comap (fun x => f x)).edgeSet
          {e | Sym2.map (fun x => f x) e = s(a, b)}
      obtain ⟨H, hHK, hH⟩ := exists_le_edge_ncard (l := l) (H' ⊓ G.comap (fun x => f x))
        (by omega)
      refine ⟨H, hH, ⟨⟨⟨fun x => f x, ?_⟩, f.injective⟩⟩⟩
      intro x y hxy
      exact (hHK hxy).2
  have hle : forcingNumber n k l ≤ forcingNumber n k l' - 1 := Nat.sInf_le hkey
  omega

theorem sq_div_four_le_choose {k l : ℕ} (h1 : k < l) (h2 : l ≤ k ^ 2 / 4) :
    k ^ 2 / 4 ≤ k.choose 2 := by
  rw [Nat.choose_two_right]
  have h4 : k ^ 2 / 4 * 4 ≤ k ^ 2 := Nat.div_mul_le_self _ _
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  rcases k with _ | _ | j
  · omega
  · omega
  · simp only [Nat.add_sub_cancel]
    nlinarith [Nat.zero_le (j * j)]

end Erdos766Aux

theorem OMA.solution : type_of% @Erdos766.erdos_766.parts.ii := by
  intro k
  filter_upwards [Filter.eventually_ge_atTop k] with n hn
  intro l hl l' hl' hll
  exact Erdos766Aux.forcingNumber_lt hn
    (le_trans hl.2 (Erdos766Aux.sq_div_four_le_choose hl.1 hl.2)) hll
