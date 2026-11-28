import OMAStatements.S_opg_triangle_packing_vs_triangle_edge_transversal

/-!
# Tuza: the edge-heavy case and the tight-perturbation case

Credit: @MBimrose

Tuza's conjecture says that a graph with at most `k` edge-disjoint triangles has a set of at most
`2 * k` edges meeting every triangle. It is open; the naive minimal-counterexample reduction (delete
an edge that lies in at most one triangle) loses exactly one unit of the budget, so it does not go
through. This file isolates the two cases that a proof has to settle, and proves that they suffice.

* `H1` (edge-heavy case): every edge of `G` lies in at least two distinct triangles. This is where
  the tight examples live: in `K_4` every edge lies in two triangles and the ratio is exactly 2.
* `H2` (tight-perturbation case): `T` is a maximum packing, the edge `xy` lies in at most one
  triangle of `G`, and no member of `T` uses `xy`. Then `G` still has a transversal of size
  `2 * |T|`, i.e. the extra triangle through `xy` can be absorbed for free. This is exactly the gap
  in the minimal-counterexample argument, stated as a standalone claim.

`main` proves the target from the two, by strong induction on the number of edges: if some edge
`xy` lies in at most one triangle, remove it; a maximum packing of the smaller graph either drops
below `|T|` (then induction plus the removed edge is enough) or has size `|T|` (then `H2` applies).

The known literature landmarks, for orientation: `tau <= 3 * nu` is the easy maximal-packing bound
(also formalised, see the lane notes), `tau <= (165/59) * nu` is the best published general bound
(S. Wang, arXiv:2609.13831), and the fractional relaxation `tau* <= 2 * nu` is a theorem and is
tight (Tuza's conjecture would follow from the integrality gap `tau <= 2 * tau*`).
-/

namespace OMA.R_opg_triangle_packing_vs_triangle_edge_transversal_R1

/-- A packing: pairwise edge-disjoint triangles (two distinct triangles are edge-disjoint exactly
when they share at most one vertex). -/
private def IsPak {V : Type} [DecidableEq V] (G : SimpleGraph V) (T : Finset (Finset V)) : Prop :=
  (∀ t ∈ T, G.IsNClique 3 t) ∧ (∀ t ∈ T, ∀ u ∈ T, t ≠ u → (t ∩ u).card ≤ 1)

/-- A packing of maximum cardinality. -/
private def MaxPak {V : Type} [DecidableEq V] (G : SimpleGraph V) (T : Finset (Finset V)) : Prop :=
  IsPak G T ∧ ∀ U : Finset (Finset V), IsPak G U → U.card ≤ T.card

/-- Every edge of `G` lies in at least two distinct triangles of `G`. -/
private def EdgeHeavy {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ x y : V, G.Adj x y →
    ∃ t1 : Finset V, G.IsNClique 3 t1 ∧ x ∈ t1 ∧ y ∈ t1 ∧
      ∃ t2 : Finset V, G.IsNClique 3 t2 ∧ x ∈ t2 ∧ y ∈ t2 ∧ t1 ≠ t2

/-- The pair `{x, y}` lies in at most one triangle of `G`. -/
private def AtMostOneTri {V : Type} (G : SimpleGraph V) (x y : V) : Prop :=
  ∀ t1 : Finset V, G.IsNClique 3 t1 → x ∈ t1 → y ∈ t1 →
    ∀ t2 : Finset V, G.IsNClique 3 t2 → x ∈ t2 → y ∈ t2 → t1 = t2

/-- `S` meets every triangle of `G`. -/
private def Hits {V : Type} (G : SimpleGraph V) (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges (S : Set (Sym2 V))).CliqueFree 3

def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T : Finset (Finset V)),
    MaxPak G T → EdgeHeavy G →
    ∃ S : Finset (Sym2 V), S.card ≤ 2 * T.card ∧ Hits G S

def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T : Finset (Finset V)) (x y : V),
    MaxPak G T → G.Adj x y → AtMostOneTri G x y → (∀ t ∈ T, ¬ (x ∈ t ∧ y ∈ t)) →
    ∃ S : Finset (Sym2 V), S.card ≤ 2 * T.card ∧ Hits G S

theorem main : H1 → H2 → type_of% @OMA.S_opg_triangle_packing_vs_triangle_edge_transversal.main := by
  intro h1 h2 V _instF _instD G k hk
  classical
  let ecard : SimpleGraph V → ℕ := fun H => H.edgeSet.ncard
  -- a packing of maximum cardinality always exists
  have exists_max : ∀ (H : SimpleGraph V), ∃ T : Finset (Finset V), MaxPak H T := by
    intro H
    have hne : ((Finset.univ : Finset (Finset V)).powerset.filter (fun T => IsPak H T)).Nonempty := by
      refine ⟨∅, ?_⟩
      simp [IsPak]
    obtain ⟨T, hTmem, hTmax⟩ :=
      Finset.exists_max_image _ (fun T : Finset (Finset V) => T.card) hne
    refine ⟨T, (Finset.mem_filter.mp hTmem).2, ?_⟩
    intro U hU
    exact hTmax U (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ U), hU⟩)
  -- strong induction on the number of edges
  have key : ∀ n : ℕ, ∀ (H : SimpleGraph V), ecard H = n → ∀ T : Finset (Finset V),
      MaxPak H T → ∃ S : Finset (Sym2 V), S.card ≤ 2 * T.card ∧ Hits H S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H hcard T hT
      by_cases hheavy : EdgeHeavy H
      · exact h1 V H T hT hheavy
      · rw [EdgeHeavy] at hheavy
        -- some edge lies in at most one triangle
        have hex : ∃ x y : V, H.Adj x y ∧ AtMostOneTri H x y := by
          by_contra hc
          apply hheavy
          intro x y hxy
          by_contra hc2
          exact hc ⟨x, y, hxy, fun t1 ht1 hx1 hy1 t2 ht2 hx2 hy2 => by
            by_contra hne
            exact hc2 ⟨t1, ht1, hx1, hy1, t2, ht2, hx2, hy2, hne⟩⟩
        obtain ⟨x, y, hxy, hone⟩ := hex
        have hxye : s(x, y) ∈ H.edgeSet := (SimpleGraph.mem_edgeSet H).mpr hxy
        -- a maximum packing of the graph with the edge xy removed
        obtain ⟨T2, hT2⟩ := exists_max (H.deleteEdges ({s(x, y)} : Set (Sym2 V)))
        have hmono : IsPak H T2 := by
          obtain ⟨hp, hd⟩ := hT2.1
          exact ⟨fun t ht => ⟨SimpleGraph.IsClique.mono (SimpleGraph.deleteEdges_le _) (hp t ht).isClique,
            (hp t ht).card_eq⟩, hd⟩
        have hle : T2.card ≤ T.card := hT.2 T2 hmono
        rcases lt_or_eq_of_le hle with hlt | heq
        · -- the packing dropped: induct on the smaller graph and add the removed edge
          have hssub : (H.deleteEdges ({s(x, y)} : Set (Sym2 V))).edgeSet ⊂ H.edgeSet := by
            rw [SimpleGraph.edgeSet_deleteEdges]
            refine Set.ssubset_iff_subset_ne.mpr ⟨Set.sdiff_subset, ?_⟩
            intro heq2
            have hmem2 : s(x, y) ∈ H.edgeSet \ ({s(x, y)} : Set (Sym2 V)) := by
              rw [heq2]
              exact hxye
            exact hmem2.2 (by simp)
          have hcardlt : ecard (H.deleteEdges ({s(x, y)} : Set (Sym2 V))) < n := by
            rw [← hcard]
            exact Set.ncard_lt_ncard hssub
          obtain ⟨S, hS, hcf⟩ := ih _ hcardlt (H.deleteEdges ({s(x, y)} : Set (Sym2 V))) rfl T2 hT2
          refine ⟨S ∪ {s(x, y)}, ?_, ?_⟩
          · have hsmall : (S ∪ {s(x, y)}).card ≤ S.card + 1 := by
              simpa using Finset.card_union_le S ({s(x, y)} : Finset (Sym2 V))
            omega
          · have hEq : H.deleteEdges ((S ∪ {s(x, y)} : Finset (Sym2 V)) : Set (Sym2 V))
                = (H.deleteEdges ({s(x, y)} : Set (Sym2 V))).deleteEdges (S : Set (Sym2 V)) := by
              ext a b
              simp only [SimpleGraph.deleteEdges_adj, Finset.coe_union, Finset.coe_singleton,
                Finset.mem_coe, Set.mem_union, Set.mem_singleton_iff]
              tauto
            rw [Hits, hEq]
            exact hcf
        · -- the packing did not drop: T2 is maximum in G and avoids xy, so H2 applies
          have hmaxH : MaxPak H T2 := ⟨hmono, fun U hU => by rw [heq]; exact hT.2 U hU⟩
          have hno : ∀ t ∈ T2, ¬ (x ∈ t ∧ y ∈ t) := by
            rintro t ht ⟨hxt, hyt⟩
            have hne : x ≠ y := SimpleGraph.ne_of_adj H hxy
            have hadj : (H.deleteEdges ({s(x, y)} : Set (Sym2 V))).Adj x y :=
              (hT2.1.1 t ht).isClique hxt hyt hne
            rw [SimpleGraph.deleteEdges_adj] at hadj
            exact hadj.2 (by simp)
          obtain ⟨S, hS, hcf⟩ := h2 V H T2 x y hmaxH hxy hone hno
          refine ⟨S, ?_, hcf⟩
          simp only [heq] at hS
          exact hS
  -- assemble the target
  obtain ⟨T, hT⟩ := exists_max G
  have hTk : T.card ≤ k := hk T hT.1.1 hT.1.2
  obtain ⟨S, hS, hcf⟩ := key (ecard G) G rfl T hT
  exact ⟨S, by omega, hcf⟩

end OMA.R_opg_triangle_packing_vs_triangle_edge_transversal_R1
