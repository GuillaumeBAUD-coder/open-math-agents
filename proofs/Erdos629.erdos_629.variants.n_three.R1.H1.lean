import OMAReductions.R_Erdos629_erdos_629_variants_n_three_R1

/-! Use the seven lines of the Fano plane as the lists on both sides of K₇,₇.
The hypergraph-to-bipartite construction is from the checked property B variant of Erdős 629. -/
open SimpleGraph
lemma OMA.property_b_choosable_mono {V : Type*} {G : SimpleGraph V} {k l : ℕ}
    (hkl : k ≤ l) (hk : G.IsKChoosable k) : G.IsKChoosable l := by
  intro L hL
  have hex (v : V) : ∃ M ⊆ L v, (M : Finset ℕ).card = k :=
    Finset.exists_subset_card_eq (by rw [hL]; exact hkl)
  choose M hM_sub hM_card using hex
  obtain ⟨C, hC⟩ := hk M hM_card
  exact ⟨C, fun v => hM_sub v (hC v)⟩

lemma OMA.property_b_finite_choosable {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.IsKChoosable (Fintype.card V) := by
  intro L hL
  have hHall (S : Finset V) : S.card ≤ (S.biUnion L).card := by
    by_cases hS : S.Nonempty
    · obtain ⟨v, hv⟩ := hS
      calc
        S.card ≤ Fintype.card V := Finset.card_le_univ S
        _ = (L v).card := (hL v).symm
        _ ≤ (S.biUnion L).card := Finset.card_le_card fun c hc =>
          Finset.mem_biUnion.mpr ⟨v, hv, hc⟩
    · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [hEmpty]
  obtain ⟨c, hc_inj, hc_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' L).mp hHall
  exact ⟨Coloring.mk c (fun h => hc_inj.ne h.ne), hc_mem⟩

lemma OMA.property_b_to_bipartite {k m : ℕ} (H : Finset (Finset (Fin m)))
    (hU : H.IsUniform k) (hNot : ¬ H.HypergraphColorable 2) :
    ∃ G : SimpleGraph (Fin (2 * H.card)), G.Colorable 2 ∧ k < G.listChromaticNumber := by
  classical
  let e : Fin (2 * H.card) ≃ Fin 2 × ↥H :=
    Fintype.equivOfCardEq (by simp [Fintype.card_prod])
  let G : SimpleGraph (Fin (2 * H.card)) :=
    { Adj := fun a b => (e a).1 ≠ (e b).1
      symm := ⟨fun _ _ h => Ne.symm h⟩
      loopless := ⟨fun _ h => h rfl⟩ }
  let L (v : Fin (2 * H.card)) : Finset ℕ := (e v).2.val.map Fin.valEmbedding
  have hL (v : Fin (2 * H.card)) : (L v).card = k := by
    rw [show L v = (e v).2.val.map Fin.valEmbedding from rfl, Finset.card_map]
    exact hU _ (e v).2.property
  have hBad : ¬ G.IsKChoosable k := by
    intro h
    obtain ⟨C, hC⟩ := h L hL
    let color (x : Fin m) : Fin 2 :=
      if ∃ ed : ↥H, C (e.symm (0, ed)) = x.val then 0 else 1
    apply hNot
    refine ⟨color, ?_⟩
    intro edge he
    let E : ↥H := ⟨edge, he⟩
    have hleft : C (e.symm (0, E)) ∈ edge.map Fin.valEmbedding := by
      simpa only [L, e.apply_symm_apply] using hC (e.symm (0, E))
    have hright : C (e.symm (1, E)) ∈ edge.map Fin.valEmbedding := by
      simpa only [L, e.apply_symm_apply] using hC (e.symm (1, E))
    obtain ⟨x, hx, hx_eq⟩ := Finset.mem_map.mp hleft
    obtain ⟨y, hy, hy_eq⟩ := Finset.mem_map.mp hright
    have h0 : color x = 0 := if_pos ⟨E, hx_eq.symm⟩
    have h1 : color y = 1 := by
      apply if_neg
      rintro ⟨F, hF⟩
      have hAdj : G.Adj (e.symm (0, F)) (e.symm (1, E)) := by
        change (e (e.symm (0, F))).1 ≠ (e (e.symm (1, E))).1
        simp
      exact C.valid hAdj (hF.trans hy_eq)
    exact ⟨x, hx, y, hy, by rw [h0, h1]; decide⟩
  have hs : {j : ℕ | G.IsKChoosable j}.Nonempty :=
    ⟨Fintype.card (Fin (2 * H.card)), OMA.property_b_finite_choosable G⟩
  have hmin : G.IsKChoosable G.listChromaticNumber := Nat.sInf_mem hs
  refine ⟨G, ⟨Coloring.mk (fun v => (e v).1) (fun h => h)⟩, ?_⟩
  by_contra! hle
  exact hBad (OMA.property_b_choosable_mono hle hmin)

private def lines : Finset (Finset (Fin 7)) :=
  {{0,1,3}, {1,2,4}, {2,3,5}, {3,4,6}, {4,5,0}, {5,6,1}, {6,0,2}}

theorem OMA.solution : OMA.R_Erdos629_erdos_629_variants_n_three_R1.H1 := by
  have hU : lines.IsUniform 3 := by unfold Finset.IsUniform; decide +kernel
  have hN : ¬ lines.HypergraphColorable 2 := by
    rintro ⟨f,hf⟩
    have hn : ∀ g : Fin 7 → Fin 2, ∃ e ∈ lines, ∀ x ∈ e, ∀ y ∈ e, g x = g y := by decide +kernel
    obtain ⟨e,he,hm⟩ := hn f
    obtain ⟨x,hx,y,hy,hxy⟩ := hf e he
    exact hxy (hm _ hx _ hy)
  obtain ⟨G,hG,hL⟩ := OMA.property_b_to_bipartite lines hU hN
  change Erdos629.n 3 ≤ 14
  have hcard : lines.card = 7 := by decide +kernel
  simpa only [hcard] using Erdos629.n_le G hG hL
