import OMAReductions.R_Erdos917_erdos_917_variants_lower_construction_R1

-- Step Erdos917.erdos_917.variants.lower_construction.R1.H1: hypothesis H1 of reduction Erdos917.erdos_917.variants.lower_construction.R1
-- Credit: @OrangeHeadz
-- H1 := ∀ b : ℕ, Odd b → 3 ≤ b → (∃ G : SimpleGraph (Fin (b)), Erdos917.IsKCritical G (3) ∧ G.edgeSet.ncard = (b))  /-- Dirac's join: the join of a `k₁`-critical and a `k₂`-critical graph is `(k₁ + k₂)`-critical. -/

/-! # An odd cycle is `3`-critical and has as many edges as vertices

For odd `b = n + 3` take the cycle graph on `Fin (n + 3)`. Its chromatic number is `3`.
Fix a vertex `u` and colour `w` by the parity of `(w - (u + 1)).val`, the position of `w` on the
path that starts at `u + 1` and runs round the cycle to `u`. Along every cycle edge other than
`{u, u + 1}` the position changes by exactly one, so this is a proper `2`-colouring of the cycle
with that edge removed, and in particular of the cycle with the vertex `u` removed. Hence deleting
any vertex or any edge lowers the chromatic number. Every vertex has degree `2`, so the handshake
identity gives `n + 3` edges. -/

open SimpleGraph

lemma OMA.col_ne (n : ℕ) (u w : Fin (n + 3)) (hw : w ≠ u) :
    ((w + 1 - (u + 1) : Fin (n + 3)).val % 2) ≠ ((w - (u + 1) : Fin (n + 3)).val % 2) := by
  have hx : (w - (u + 1) : Fin (n + 3)) ≠ Fin.last (n + 2) := by
    intro h
    apply hw
    have h1 : w - (u + 1) + 1 = 0 := by rw [h]; exact Fin.last_add_one _
    have h2 : w - u = 0 := by rw [← h1]; abel
    exact sub_eq_zero.1 h2
  have hlt : (w - (u + 1) : Fin (n + 3)) < Fin.last (n + 2) := lt_of_le_of_ne (Fin.le_last _) hx
  have e : (w + 1 - (u + 1) : Fin (n + 3)) = (w - (u + 1)) + 1 := by abel
  rw [e, Fin.val_add_one_of_lt hlt]
  omega

lemma OMA.col_adj (n : ℕ) (u w w' : Fin (n + 3)) (hadj : (cycleGraph (n + 3)).Adj w w')
    (h1 : ¬ (w = u ∧ w' = u + 1)) (h2 : ¬ (w' = u ∧ w = u + 1)) :
    ((w - (u + 1) : Fin (n + 3)).val % 2) ≠ ((w' - (u + 1) : Fin (n + 3)).val % 2) := by
  rw [cycleGraph_adj] at hadj
  rcases hadj with h | h
  · have hw : w = w' + 1 := by rw [← h]; abel
    subst hw
    exact OMA.col_ne n u w' (fun h' => h2 ⟨h', by rw [h']⟩)
  · have hw : w' = w + 1 := by rw [← h]; abel
    subst hw
    exact (OMA.col_ne n u w (fun h' => h1 ⟨h', by rw [h']⟩)).symm

theorem OMA.solution : OMA.R_Erdos917_erdos_917_variants_lower_construction_R1.H1 := by
  intro b hodd hb
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 3 := ⟨b - 3, by omega⟩
  have hχ : (cycleGraph (n + 3)).chromaticNumber = 3 :=
    chromaticNumber_cycleGraph_of_odd (n + 3) (by omega) hodd
  have h23 : ((2 : ℕ) : ℕ∞) < 3 := by exact_mod_cast (by norm_num : (2 : ℕ) < 3)
  have hpath : ∀ u : Fin (n + 3),
      ((cycleGraph (n + 3)).deleteEdges {s(u, u + 1)}).Colorable 2 := by
    intro u
    refine ⟨Coloring.mk (fun w =>
      (⟨(w - (u + 1) : Fin (n + 3)).val % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)) ?_⟩
    intro w w' hadj
    rw [deleteEdges_adj] at hadj
    obtain ⟨hadj, hne⟩ := hadj
    have key := OMA.col_adj n u w w' hadj
      (fun h => hne (by rw [h.1, h.2]; rfl))
      (fun h => hne (by rw [h.1, h.2]; exact Sym2.eq_swap))
    intro heq
    exact key (Fin.mk.inj heq)
  refine ⟨cycleGraph (n + 3), ⟨⟨hχ, ?_⟩, ?_⟩, ?_⟩
  · intro v
    show ((⊤ : (cycleGraph (n + 3)).Subgraph).deleteVerts {v}).coe.chromaticNumber <
      (⊤ : (cycleGraph (n + 3)).Subgraph).coe.chromaticNumber
    have htop : (⊤ : (cycleGraph (n + 3)).Subgraph).coe.chromaticNumber = 3 := by
      rw [← hχ]
      exact le_antisymm (chromaticNumber_mono_of_hom Subgraph.topIso.toHom)
        (chromaticNumber_mono_of_hom Subgraph.topIso.symm.toHom)
    have hcol : ((⊤ : (cycleGraph (n + 3)).Subgraph).deleteVerts {v}).coe.Colorable 2 := by
      refine ⟨Coloring.mk (fun w =>
        (⟨(w.1 - (v + 1) : Fin (n + 3)).val % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)) ?_⟩
      intro w w' hadj
      have hG : (cycleGraph (n + 3)).Adj w.1 w'.1 := Subgraph.coe_adj_sub _ _ _ hadj
      have hw : w.1 ≠ v := by
        have := w.2
        simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_sdiff, Set.mem_univ,
          Set.mem_singleton_iff, true_and] at this
        exact this
      have hw' : w'.1 ≠ v := by
        have := w'.2
        simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_sdiff, Set.mem_univ,
          Set.mem_singleton_iff, true_and] at this
        exact this
      have key := OMA.col_adj n v w.1 w'.1 hG (fun h => hw h.1) (fun h => hw' h.1)
      intro heq
      exact key (Fin.mk.inj heq)
    rw [htop]
    exact lt_of_le_of_lt hcol.chromaticNumber_le h23
  · intro e he
    induction e using Sym2.ind with
    | _ w w' =>
      have hadj : (cycleGraph (n + 3)).Adj w w' := he
      show ((cycleGraph (n + 3)).deleteEdges {s(w, w')}).chromaticNumber <
        (cycleGraph (n + 3)).chromaticNumber
      rw [hχ]
      have hc : ((cycleGraph (n + 3)).deleteEdges {s(w, w')}).Colorable 2 := by
        have h' := hadj
        rw [cycleGraph_adj] at h'
        rcases h' with h | h
        · have hw : w = w' + 1 := by rw [← h]; abel
          rw [hw, Sym2.eq_swap]
          exact hpath w'
        · have hw : w' = w + 1 := by rw [← h]; abel
          rw [hw]
          exact hpath w
      exact lt_of_le_of_lt hc.chromaticNumber_le h23
  · classical
    have hdeg : ∀ v : Fin (n + 3), (cycleGraph (n + 3)).degree v = 2 :=
      fun v => cycleGraph_degree_three_le
    have hsum := (cycleGraph (n + 3)).sum_degrees_eq_twice_card_edges
    simp only [hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
    omega
