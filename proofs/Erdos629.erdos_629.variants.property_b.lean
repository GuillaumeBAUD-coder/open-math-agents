import FormalConjectures.ErdosProblems.«629»

/-! Compare uncolorable uniform families with obstructions to bipartite list colorings. -/

open SimpleGraph

lemma OMA.property_b_extract_three {V : Type*} [DecidableEq V] (H : Finset (Finset V))
    (k : ℕ) (hk : 2 ≤ k) (hU : H.IsUniform k) (hNot : ¬ H.HypergraphColorable 2) :
    ∃ J ⊆ H, J.IsUniform k ∧ J.HasHypergraphChromaticNumber 3 := by
  classical
  let bad := H.powerset.filter fun J => ¬ J.HypergraphColorable 2
  have hbad : bad.Nonempty :=
    ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (fun _ h => h), hNot⟩⟩
  obtain ⟨J, hJ, hmin⟩ := bad.exists_min_image Finset.card hbad
  obtain ⟨hJ_mem, hJ_not⟩ := Finset.mem_filter.mp hJ
  have hJ_sub := Finset.mem_powerset.mp hJ_mem
  have hJ_U : J.IsUniform k := fun e he => hU e (hJ_sub he)
  have hJ_ne : J.Nonempty := by
    by_contra h
    have hEmpty := Finset.not_nonempty_iff_eq_empty.mp h
    exact hJ_not ⟨fun _ => 0, by simp [hEmpty, Finset.IsProperHypergraphColoring]⟩
  obtain ⟨e, he⟩ := hJ_ne
  have hErase : (J.erase e).HypergraphColorable 2 := by
    by_contra h
    have hbadErase : J.erase e ∈ bad := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ((Finset.erase_subset e J).trans hJ_sub), h⟩
    have hle := hmin _ hbadErase
    have hpos := Finset.card_pos.mpr (show J.Nonempty from ⟨e, he⟩)
    rw [Finset.card_erase_of_mem he] at hle
    omega
  obtain ⟨col, hcol⟩ := hErase
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (show 1 < e.card by rw [hJ_U e he]; omega)
  let extend (x : V) : Fin 3 := if x = a then 2 else Fin.castLE (by decide : 2 ≤ 3) (col x)
  have hA : extend a = 2 := if_pos rfl
  have hOther (x : V) (hx : x ≠ a) :
      extend x = Fin.castLE (by decide : 2 ≤ 3) (col x) := if_neg hx
  have hDifferent : ∀ t : Fin 2, Fin.castLE (by decide : 2 ≤ 3) t ≠ 2 := by decide
  refine ⟨J, hJ_sub, hJ_U, ⟨extend, ?_⟩, ?_⟩
  · intro f hf
    by_cases hfe : f = e
    · subst f
      refine ⟨a, ha, b, hb, ?_⟩
      rw [hA, hOther b hab.symm]
      exact (hDifferent _).symm
    · obtain ⟨x, hx, y, hy, hxy⟩ := hcol f (Finset.mem_erase.mpr ⟨hfe, hf⟩)
      refine ⟨x, hx, y, hy, ?_⟩
      have hne : x ≠ y := fun h => hxy (congrArg col h)
      by_cases hxa : x = a
      · subst x
        rw [hA, hOther y hne.symm]
        exact (hDifferent _).symm
      · rw [hOther x hxa]
        by_cases hya : y = a
        · subst y
          rw [hA]
          exact hDifferent _
        · rw [hOther y hya]
          exact (Fin.castLE_injective (by decide : 2 ≤ 3)).ne hxy
  · intro j hj hJcol
    obtain ⟨c, hc⟩ := hJcol
    have hj' : j ≤ 2 := by omega
    apply hJ_not
    refine ⟨fun x => Fin.castLE hj' (c x), ?_⟩
    intro f hf
    obtain ⟨x, hx, y, hy, hxy⟩ := hc f hf
    exact ⟨x, hx, y, hy, (Fin.castLE_injective hj').ne hxy⟩

lemma OMA.property_b_finite_witness (k : ℕ) (hk : 2 ≤ k) :
    ∃ (m : ℕ) (H : Finset (Finset (Fin m))), H.IsUniform k ∧ H.HasHypergraphChromaticNumber 3 := by
  classical
  let m := 2 * k - 1
  let H := (Finset.univ : Finset (Fin m)).powersetCard k
  have hU : H.IsUniform k := fun e he => (Finset.mem_powersetCard.mp he).2
  have hNot : ¬ H.HypergraphColorable 2 := by
    rintro ⟨c, hc⟩
    let A : Finset (Fin m) := Finset.univ.filter fun x => c x = 0
    let B : Finset (Fin m) := Finset.univ \ A
    have hB : B.card = m - A.card := by
      dsimp [B]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have hmono (b : Fin 2) (S : Finset (Fin m)) (hs : k ≤ S.card)
        (hcol : ∀ x ∈ S, c x = b) : False := by
      obtain ⟨e, heS, heCard⟩ := Finset.exists_subset_card_eq hs
      have he : e ∈ H := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, heCard⟩
      obtain ⟨x, hx, y, hy, hne⟩ := hc e he
      exact hne ((hcol x (heS hx)).trans (hcol y (heS hy)).symm)
    by_cases hA : k ≤ A.card
    · exact hmono 0 A hA (fun x hx => (Finset.mem_filter.mp hx).2)
    · have hBcard : k ≤ B.card := by dsimp [m] at hB; omega
      apply hmono 1 B hBcard
      intro x hx
      have hxA := (Finset.mem_sdiff.mp hx).2
      have hx0 : c x ≠ 0 := fun h => hxA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have hcases : ∀ t : Fin 2, t ≠ 0 → t = 1 := by decide
      exact hcases _ hx0
  obtain ⟨J, _, hJ_U, hJ_col⟩ := OMA.property_b_extract_three H k hk hU hNot
  exact ⟨m, J, hJ_U, hJ_col⟩

lemma OMA.property_b_min_le {k m : ℕ} (H : Finset (Finset (Fin m))) (hU : H.IsUniform k)
    (hC : H.HasHypergraphChromaticNumber 3) :
    Hypergraph.minChromaticEdges k 3 ≤ (H.card : ENat) := by
  unfold Hypergraph.minChromaticEdges
  exact iInf_le_of_le m (iInf_le_of_le H (iInf_le_of_le hU (iInf_le_of_le hC le_rfl)))

lemma OMA.property_b_min_attains (k : ℕ) (hk : 2 ≤ k) :
    ∃ (m : ℕ) (H : Finset (Finset (Fin m))), H.IsUniform k ∧ H.HasHypergraphChromaticNumber 3 ∧
      Hypergraph.minChromaticEdges k 3 = (H.card : ENat) := by
  let sizes : Set ℕ := {d | ∃ (m : ℕ) (J : Finset (Finset (Fin m))),
    J.IsUniform k ∧ J.HasHypergraphChromaticNumber 3 ∧ J.card = d}
  obtain ⟨m₀, H₀, hU₀, hC₀⟩ := OMA.property_b_finite_witness k hk
  have hs : sizes.Nonempty := ⟨H₀.card, m₀, H₀, hU₀, hC₀, rfl⟩
  obtain ⟨m, H, hU, hC, hCard⟩ := Nat.sInf_mem hs
  refine ⟨m, H, hU, hC, le_antisymm (OMA.property_b_min_le H hU hC) ?_⟩
  rw [hCard]
  unfold Hypergraph.minChromaticEdges
  refine le_iInf fun n => le_iInf fun J => le_iInf fun hJ_U => le_iInf fun hJ_C => ?_
  exact_mod_cast (Nat.sInf_le (show J.card ∈ sizes from ⟨n, J, hJ_U, hJ_C, rfl⟩))

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

lemma OMA.property_b_from_bipartite {k n : ℕ} (hk : 2 ≤ k) (G : SimpleGraph (Fin n))
    (hG : G.Colorable 2) (hBad : ¬ G.IsKChoosable k) :
    ∃ (m : ℕ) (H : Finset (Finset (Fin m))), H.IsUniform k ∧ H.HasHypergraphChromaticNumber 3 ∧ H.card ≤ n := by
  classical
  have hObstruction : ∃ L : Fin n → Finset ℕ, (∀ v, (L v).card = k) ∧
      ¬ ∃ C : G.Coloring ℕ, ∀ v, C v ∈ L v := by
    by_contra h
    apply hBad
    intro L hL
    by_contra hC
    exact h ⟨L, hL, hC⟩
  obtain ⟨L, hL, hNo⟩ := hObstruction
  obtain ⟨C⟩ := hG
  let P := (Finset.univ : Finset (Fin n)).biUnion L
  let e : ↥P ≃ Fin P.card := Fintype.equivFinOfCardEq (by simp)
  have hsub (v : Fin n) : L v ⊆ P := fun x hx =>
    Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hx⟩
  let mapColor (v : Fin n) : ↥(L v) ↪ Fin P.card :=
    ⟨fun x => e ⟨x.val, hsub v x.property⟩,
      fun _ _ h => Subtype.ext (congrArg (fun p : ↥P => p.val) (e.injective h))⟩
  let lists (v : Fin n) := (L v).attach.map (mapColor v)
  let H := (Finset.univ : Finset (Fin n)).image lists
  have hU : H.IsUniform k := by
    intro edge he
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp he
    dsimp [lists]
    rw [Finset.card_map, Finset.card_attach, hL]
  have hNot : ¬ H.HypergraphColorable 2 := by
    rintro ⟨c, hc⟩
    have hget (v : Fin n) {t : Fin P.card} (ht : t ∈ lists v) :
        ∃ q : ↥P, q.val ∈ L v ∧ e q = t := by
      obtain ⟨a, _, ha⟩ := Finset.mem_map.mp ht
      exact ⟨⟨a.val, hsub v a.property⟩, a.property, ha⟩
    have hselect (v : Fin n) : ∃ q : ↥P, q.val ∈ L v ∧ c (e q) = C v := by
      have hvH : lists v ∈ H := Finset.mem_image_of_mem lists (Finset.mem_univ _)
      obtain ⟨x, hx, y, hy, hxy⟩ := hc (lists v) hvH
      have hcases : ∀ a b d : Fin 2, a ≠ b → a = d ∨ b = d := by decide
      rcases hcases (c x) (c y) (C v) hxy with hal | har
      · obtain ⟨q, hq, hqe⟩ := hget v hx
        exact ⟨q, hq, hqe.symm ▸ hal⟩
      · obtain ⟨q, hq, hqe⟩ := hget v hy
        exact ⟨q, hq, hqe.symm ▸ har⟩
    choose q hqL hqColor using hselect
    have hValid : ∀ {a b}, G.Adj a b → (q a).val ≠ (q b).val := by
      intro a b hab heq
      have hqEq : q a = q b := Subtype.ext heq
      apply C.valid hab
      rw [← hqColor a, ← hqColor b, hqEq]
    exact hNo ⟨Coloring.mk (fun v => (q v).val) hValid, hqL⟩
  obtain ⟨J, hSub, hJ_U, hJ_col⟩ := OMA.property_b_extract_three H k hk hU hNot
  have hH_card : H.card ≤ n := by
    exact Finset.card_image_le.trans_eq (by simp)
  exact ⟨P.card, J, hJ_U, hJ_col, (Finset.card_le_card hSub).trans hH_card⟩

theorem OMA.solution : type_of% @Erdos629.erdos_629.variants.property_b := by
  intro k hk
  obtain ⟨m, H, hU, hC, hmin⟩ := OMA.property_b_min_attains k hk
  have hNot : ¬ H.HypergraphColorable 2 := hC.2 2 (by decide)
  obtain ⟨G, hG, hGList⟩ := OMA.property_b_to_bipartite H hU hNot
  have hUpper : Erdos629.n k ≤ 2 * H.card := Erdos629.n_le G hG hGList
  have hex : {v : ℕ | ∃ J : SimpleGraph (Fin v),
      J.Colorable 2 ∧ k < J.listChromaticNumber}.Nonempty :=
    ⟨2 * H.card, G, hG, hGList⟩
  have hGmin : ∃ J : SimpleGraph (Fin (Erdos629.n k)),
      J.Colorable 2 ∧ k < J.listChromaticNumber := Nat.sInf_mem hex
  obtain ⟨J, hJ, hJList⟩ := hGmin
  have hJBad : ¬ J.IsKChoosable k := fun h =>
    (not_le_of_gt hJList) (Nat.sInf_le h)
  obtain ⟨_, K, hK_U, hK_C, hK_card⟩ := OMA.property_b_from_bipartite hk J hJ hJBad
  have hK_min := OMA.property_b_min_le K hK_U hK_C
  rw [hmin] at hK_min
  have hK_le : H.card ≤ K.card := by exact_mod_cast hK_min
  rw [hmin, ENat.toNat_natCast]
  exact ⟨hK_le.trans hK_card, hUpper⟩