import FormalConjectures.ErdosProblems.«23»

/-! Count the monochromatic edges of any two-coloring of the balanced pentagon blow-up. -/

open SimpleGraph

def OMA.sameColorPairs (a b : Fin 6) : ℕ :=
  a.val * b.val + (5 - a.val) * (5 - b.val)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma OMA.pentagonProfile :
    ∀ a b c d e : Fin 6, 25 ≤
      OMA.sameColorPairs a b + OMA.sameColorPairs b c + OMA.sameColorPairs c d +
        OMA.sameColorPairs d e + OMA.sameColorPairs e a := by
  decide +kernel

lemma OMA.blowupAdj (x y : ZMod 5 × Fin 5) :
    (Erdos23.blowupC5 5).Adj x y ↔ x.1 + 1 = y.1 ∨ y.1 + 1 = x.1 := by
  rw [Erdos23.blowupC5, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h⟩
    tauto
  · intro h
    refine ⟨?_, Or.inl h⟩
    intro he
    rw [he] at h
    have hne : ∀ i : ZMod 5, i + 1 ≠ i := by decide +kernel
    exact h.elim (hne _) (hne _)

theorem OMA.solution : type_of% @Erdos23.erdos_23.variants.n5_tight := by
  classical
  let e : (ZMod 5 × Fin 5) ≃ Fin 25 :=
    Fintype.equivFinOfCardEq (by simp)
  let G : SimpleGraph (Fin 25) := (Erdos23.blowupC5 5).comap e.symm
  have hadj (x y : Fin 25) :
      G.Adj x y ↔ (e.symm x).1 + 1 = (e.symm y).1 ∨ (e.symm y).1 + 1 = (e.symm x).1 :=
    OMA.blowupAdj _ _
  refine ⟨G, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := SimpleGraph.is3Clique_iff.mp ht
    have htri : ∀ i j k : ZMod 5,
        ¬ ((i + 1 = j ∨ j + 1 = i) ∧ (i + 1 = k ∨ k + 1 = i) ∧
          (j + 1 = k ∨ k + 1 = j)) := by decide +kernel
    exact htri _ _ _ ⟨(hadj _ _).mp hxy, (hadj _ _).mp hxz, (hadj _ _).mp hyz⟩
  · intro H _ hBip
    obtain ⟨c⟩ := hBip
    let colors (i : ZMod 5) (j : Fin 2) := Finset.univ.filter (fun a : Fin 5 => c (e (i, a)) = j)
    have colorSum (i : ZMod 5) : (colors i 0).card + (colors i 1).card = 5 := by
      have hcolors : ∀ j : Fin 2, j ≠ 0 ↔ j = 1 := by decide +kernel
      have hcomp : colors i 1 = Finset.univ.filter (fun a : Fin 5 => c (e (i, a)) ≠ 0) := by
        ext a
        simp only [colors, Finset.mem_filter, Finset.mem_univ, true_and, hcolors]
      rw [hcomp]
      simpa [colors] using
        (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 5)))
          (fun a => c (e (i, a)) = 0))
    let a : ZMod 5 → Fin 6 := fun i => ⟨(colors i 0).card, by have h := colorSum i; omega⟩
    have otherColor (i : ZMod 5) : (colors i 1).card = 5 - (a i).val := by
      have h := colorSum i
      dsimp [a]
      omega
    let same (i : ZMod 5) :=
      (colors i 0 ×ˢ colors (i + 1) 0) ∪ (colors i 1 ×ˢ colors (i + 1) 1)
    have sameCard (i : ZMod 5) : (same i).card = OMA.sameColorPairs (a i) (a (i + 1)) := by
      have hd : Disjoint (colors i 0 ×ˢ colors (i + 1) 0) (colors i 1 ×ˢ colors (i + 1) 1) := by
        refine Finset.disjoint_left.mpr ?_
        intro p h0 h1
        have he0 := (Finset.mem_filter.mp (Finset.mem_product.mp h0).1).2
        have he1 := (Finset.mem_filter.mp (Finset.mem_product.mp h1).1).2
        exact (by decide : (0 : Fin 2) ≠ 1) (he0.symm.trans he1)
      dsimp [same]
      rw [Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product,
        otherColor i, otherColor (i + 1)]
      rfl
    let edge : (Σ _ : ZMod 5, Fin 5 × Fin 5) ↪ Sym2 (Fin 25) := ⟨
      fun p => s(e (p.1, p.2.1), e (p.1 + 1, p.2.2)), by
        rintro ⟨i, x, y⟩ ⟨j, u, v⟩ he
        change s(e (i, x), e (i + 1, y)) = s(e (j, u), e (j + 1, v)) at he
        rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (e.injective h1)
          obtain ⟨_, rfl⟩ := Prod.mk.inj (e.injective h2)
          rfl
        · have hrev : ∀ i j : ZMod 5, ¬ (i = j + 1 ∧ i + 1 = j) := by decide +kernel
          exact (hrev i j ⟨congrArg Prod.fst (e.injective h1),
            congrArg Prod.fst (e.injective h2)⟩).elim⟩
    let monochromatic : Finset (Σ _ : ZMod 5, Fin 5 × Fin 5) := Finset.univ.sigma same
    have hsub : monochromatic.map edge ⊆ G.edgeFinset \ H.edgeFinset := by
      intro z hz
      obtain ⟨⟨i, x, y⟩, hp, rfl⟩ := Finset.mem_map.mp hz
      have hsame : (x, y) ∈ same i := (Finset.mem_sigma.mp hp).2
      have heq : c (e (i, x)) = c (e (i + 1, y)) := by
        rcases Finset.mem_union.mp hsame with h | h
        all_goals
          obtain ⟨hx, hy⟩ := Finset.mem_product.mp h
          exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      change s(e (i, x), e (i + 1, y)) ∈ G.edgeFinset \ H.edgeFinset
      rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      exact ⟨(hadj _ _).mpr (Or.inl (by simp)), fun h => c.valid h heq⟩
    have hcard : 25 ≤ monochromatic.card := by
      dsimp [monochromatic]
      rw [Finset.card_sigma]
      simp only [sameCard]
      change 25 ≤ ∑ i : Fin 5, OMA.sameColorPairs (a i) (a ((fun j : ZMod 5 => j + 1) i))
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      change 25 ≤ OMA.sameColorPairs (a 0) (a 1) +
        (OMA.sameColorPairs (a 1) (a 2) +
          (OMA.sameColorPairs (a 2) (a 3) +
            (OMA.sameColorPairs (a 3) (a 4) + OMA.sameColorPairs (a 4) (a 0))))
      simpa only [add_assoc] using OMA.pentagonProfile (a 0) (a 1) (a 2) (a 3) (a 4)
    exact hcard.trans ((Finset.card_map edge).ge.trans (Finset.card_le_card hsub))