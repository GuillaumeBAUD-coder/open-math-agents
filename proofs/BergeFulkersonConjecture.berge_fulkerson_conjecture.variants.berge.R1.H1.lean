import OMAReductions.R_BergeFulkersonConjecture_berge_fulkerson_conjecture_variants_berge_R1

/-! Properly 3-edge-colored cubic graphs have three perfect matchings covering every edge. -/

-- Step BergeFulkersonConjecture.berge_fulkerson_conjecture.variants.berge.R1.H1: hypothesis H1 of reduction BergeFulkersonConjecture.berge_fulkerson_conjecture.variants.berge.R1
-- Credit: @RiverMint78

open SimpleGraph BergeFulkersonConjecture

theorem OMA.solution : OMA.R_BergeFulkersonConjecture_berge_fulkerson_conjecture_variants_berge_R1.H1 := by
  classical
  rintro V _ _ G _ hcubic ⟨c⟩
  let edge {v w : V} (h : G.Adj v w) : G.edgeSet := ⟨s(v, w), G.mem_edgeSet.mpr h⟩
  have swap {v w : V} (h : G.Adj v w) : edge h = edge h.symm :=
    Subtype.ext Sym2.eq_swap
  let colorAt (v : V) (w : G.neighborSet v) : Fin 3 := c (edge w.property)
  -- At a fixed vertex all three incident edges receive distinct colors.
  have bij (v : V) : Function.Bijective (colorAt v) := by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
    · intro w w' eqColor
      by_contra hne
      have different : edge w.property ≠ edge w'.property := by
        intro h
        apply hne
        apply (G.incidenceSetEquivNeighborSet v).symm.injective
        apply Subtype.ext
        exact congrArg (fun e : G.edgeSet => e.val) h
      exact c.valid (lineGraph_adj_iff_exists.mpr
        ⟨different, v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩) eqColor
    · rw [G.card_neighborSet_eq_degree v, hcubic v, Fintype.card_fin]
  let matchColor (i : Fin 3) : G.Subgraph :=
    { verts := Set.univ
      Adj := fun v w => ∃ h : G.Adj v w, c (edge h) = i
      adj_sub := fun ⟨h, _⟩ => h
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨fun v w ⟨h, hi⟩ => ⟨h.symm, (congrArg c (swap h)).symm.trans hi⟩⟩ }
  have perfect (i : Fin 3) : (matchColor i).IsPerfectMatching := by
    rw [Subgraph.isPerfectMatching_iff]
    intro v
    obtain ⟨w, hw⟩ := (bij v).2 i
    refine ⟨w.val, ⟨w.property, hw⟩, ?_⟩
    rintro u ⟨hu, hcolor⟩
    exact congrArg Subtype.val ((bij v).1 (hcolor.trans hw.symm) : (⟨u, hu⟩ : G.neighborSet v) = w)
  -- Reuse two color classes to extend the three matchings to five.
  let pad (j : Fin 5) : Fin 3 := Fin.ofNat 3 j.val
  refine ⟨fun j => matchColor (pad j), fun j => perfect (pad j), ?_⟩
  rintro ⟨v,w⟩ he
  let h : G.Adj v w := G.mem_edgeSet.mp he
  let i := c (edge h)
  let j : Fin 5 := Fin.castLE (by decide : 3 ≤ 5) i
  have hj : pad j = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  exact ⟨j, Subgraph.mem_edgeSet.mpr ⟨h, hj.symm⟩⟩
