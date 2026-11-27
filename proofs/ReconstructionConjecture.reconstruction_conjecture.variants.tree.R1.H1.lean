import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1

/-!
# Path trees (`degree <= 2`) are isomorphic (`tree.R1.H1` offline pre-proof)

Every finite tree on `n + 1` vertices with maximum degree at most `2` has a vertex of degree at
most `1`, and deleting that endpoint gives an inductive isomorphism with the canonical path graph
on `Fin (n + 1)`.
-/

-- Credit: @green-notes

open SimpleGraph

section TreeR1H1

open Classical

private def pathG (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

private lemma exists_deg_le_one_of_tree {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsTree) (_hV : 1 ≤ Fintype.card V) (hdeg : ∀ v : V, G.degree v ≤ 2) :
    ∃ u : V, G.degree u ≤ 1 := by
  by_contra hno
  push Not at hno
  have htwo : ∀ v : V, G.degree v = 2 := fun v => by have := hdeg v; have := hno v; omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hcard := hG.card_edgeFinset
  simp only [htwo, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  omega

private lemma isAcyclic_induce {V : Type*} (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Set V) :
    (G.induce S).IsAcyclic := by
  intro v c hc
  let f : G.induce S →g G := ⟨Subtype.val, fun h => h⟩
  have hf : Function.Injective f := Subtype.val_injective
  exact hG (c.map f) (hc.map hf)

private lemma ncard_neighborSet_eq_degree {U : Type} [Fintype U] (Z : SimpleGraph U) (u : U) :
    (Z.neighborSet u).ncard = Z.degree u := by
  rw [← Z.card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card' (Z.neighborSet u)]
  simp [Set.toFinset_card]

private lemma path_tree_from_end :
    ∀ (n : ℕ) {V : Type} [Fintype V] (G : SimpleGraph V),
      G.IsTree → Fintype.card V = n + 1 → (∀ v : V, G.degree v ≤ 2) →
      ∀ u : V, G.degree u ≤ 1 →
      ∃ φ : G ≃g pathG (n + 1), φ u = 0 := by
  intro n
  induction n with
  | zero =>
    intro V _ G _ hcard _ u _
    have hss : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    refine ⟨⟨⟨fun _ => 0, fun _ => u, ?_, ?_⟩, ?_⟩, rfl⟩
    · intro v
      exact Subsingleton.elim u v
    · intro i
      fin_cases i
      rfl
    · intro a b
      have hab : a = b := Subsingleton.elim a b
      subst hab
      simp [pathG]
  | succ n ih =>
    intro V _ G hG hcard hdeg u hu
    have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨w, hwu⟩ := exists_ne u
    obtain ⟨p⟩ := hG.connected.preconnected u w
    have hu_deg1 : G.degree u = 1 := by
      rcases p with _ | ⟨hadj, _⟩
      · exact False.elim (hwu rfl)
      · have hpos : 0 < G.degree u := by
          rw [← G.card_neighborFinset_eq_degree]
          exact Finset.card_pos.mpr ⟨_, (G.mem_neighborFinset u _).mpr hadj⟩
        omega
    obtain ⟨u', huu', hu'_uniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hu_deg1
    let V' := ({u}ᶜ : Set V)
    let G' := G.induce V'
    have hV' : Fintype.card V' = n + 1 := by
      have eV' : V' ≃ ↥(Finset.univ.erase u) :=
        ⟨fun x => ⟨x.1, Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩⟩,
         fun x => ⟨x.1, (Finset.mem_erase.mp x.2).1⟩,
         fun _ => rfl, fun _ => rfl⟩
      rw [Fintype.card_congr eV', Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ u),
        Finset.card_univ, hcard]
      omega
    have hconn' : G'.Connected :=
      hG.connected.induce_compl_singleton_of_degree_eq_one hu_deg1
    have hG' : G'.IsTree := ⟨hconn', isAcyclic_induce G hG.isAcyclic V'⟩
    have hsub (x : V') :
        (G'.neighborFinset x).map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ G.neighborFinset x.1 := by
      intro y hy
      rw [Finset.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      rw [SimpleGraph.mem_neighborFinset] at hz ⊢
      exact hz
    have hdeg' (x : V') : G'.degree x ≤ 2 := by
      have hc : G'.degree x ≤ G.degree x.1 := by
        rw [← G'.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree,
          ← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
        exact Finset.card_le_card (hsub x)
      exact hc.trans (hdeg x.1)
    have hu'u : u' ∈ V' := huu'.ne.symm
    let x₀ : V' := ⟨u', hu'u⟩
    have hx₀_deg : G'.degree x₀ ≤ 1 := by
      have hunot : u ∉ (G'.neighborFinset x₀).map ⟨Subtype.val, Subtype.val_injective⟩ := by
        intro h
        rw [Finset.mem_map] at h
        obtain ⟨z, _, hzu⟩ := h
        exact z.2 hzu
      have hins :
          insert u ((G'.neighborFinset x₀).map ⟨Subtype.val, Subtype.val_injective⟩) ⊆
            G.neighborFinset u' := by
        intro y hy
        rcases Finset.mem_insert.mp hy with hyu | hy'
        · subst hyu
          rw [SimpleGraph.mem_neighborFinset]
          exact huu'.symm
        · exact hsub x₀ hy'
      have hc := Finset.card_le_card hins
      rw [Finset.card_insert_of_notMem hunot, Finset.card_map,
        G'.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hc
      have := hdeg u'
      omega
    obtain ⟨φ', hφ0⟩ := ih G' hG' hV' hdeg' x₀ hx₀_deg
    let toF : V → Fin (n + 2) := fun v => if hv : v = u then 0 else (φ' ⟨v, hv⟩).succ
    let invF : Fin (n + 2) → V := Fin.cases u (fun j => (φ'.symm j).val)
    have hleft : Function.LeftInverse invF toF := by
      intro v
      dsimp only [toF, invF]
      by_cases hv : v = u
      · subst hv
        simp
      · rw [dif_neg hv]
        simp
    have hright : Function.RightInverse invF toF := by
      intro i
      dsimp only [toF, invF]
      induction i using Fin.cases with
      | zero => simp
      | succ j =>
        have hne : (φ'.symm j).val ≠ u := (φ'.symm j).2
        simp [hne]
    refine ⟨⟨⟨toF, invF, hleft, hright⟩, ?_⟩, ?_⟩
    · intro a b
      dsimp only [Equiv.coe_fn_mk, toF]
      by_cases ha : a = u <;> by_cases hb : b = u
      · subst ha; subst hb
        simp [pathG]
      · subst ha
        rw [dif_pos rfl, dif_neg hb]
        constructor
        · intro hadj
          have h0 : φ' ⟨b, hb⟩ = 0 := by
            change (0 : Fin (n + 2)).val + 1 = (φ' ⟨b, hb⟩).succ.val ∨
                (φ' ⟨b, hb⟩).succ.val + 1 = (0 : Fin (n + 2)).val at hadj
            simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_succ] at hadj
            apply Fin.ext
            rw [Fin.val_zero]
            omega
          have hbx : (⟨b, hb⟩ : V') = x₀ := φ'.injective (h0.trans hφ0.symm)
          have hbu : b = u' := congrArg Subtype.val hbx
          subst hbu
          exact huu'
        · intro hadj
          have hbu : b = u' := hu'_uniq b hadj
          have hbx : (⟨b, hb⟩ : V') = x₀ := Subtype.ext hbu
          have h0 : φ' ⟨b, hb⟩ = 0 := (congrArg φ' hbx).trans hφ0
          rw [h0]
          simp [pathG]
      · subst hb
        rw [dif_neg ha, dif_pos rfl]
        constructor
        · intro hadj
          have h0 : φ' ⟨a, ha⟩ = 0 := by
            change (φ' ⟨a, ha⟩).succ.val + 1 = (0 : Fin (n + 2)).val ∨
                (0 : Fin (n + 2)).val + 1 = (φ' ⟨a, ha⟩).succ.val at hadj
            simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_succ] at hadj
            apply Fin.ext
            rw [Fin.val_zero]
            omega
          have hax : (⟨a, ha⟩ : V') = x₀ := φ'.injective (h0.trans hφ0.symm)
          have hau : a = u' := congrArg Subtype.val hax
          subst hau
          exact huu'.symm
        · intro hadj
          have hau : a = u' := hu'_uniq a hadj.symm
          have hax : (⟨a, ha⟩ : V') = x₀ := Subtype.ext hau
          have h0 : φ' ⟨a, ha⟩ = 0 := (congrArg φ' hax).trans hφ0
          rw [h0]
          simp [pathG]
      · rw [dif_neg ha, dif_neg hb]
        have hstep : (pathG (n + 2)).Adj (φ' ⟨a, ha⟩).succ (φ' ⟨b, hb⟩).succ ↔
            (pathG (n + 1)).Adj (φ' ⟨a, ha⟩) (φ' ⟨b, hb⟩) := by
          simp only [pathG, Fin.val_succ]
          omega
        exact hstep.trans (φ'.map_rel_iff (a := ⟨a, ha⟩) (b := ⟨b, hb⟩))
    · dsimp only [RelIso.coe_fn_mk, Equiv.coe_fn_mk, toF]
      exact dif_pos rfl

private lemma tree_R1_H1 :
    ∀ {V W : Type} [Fintype V] [Fintype W],
      3 ≤ Fintype.card V → Fintype.card V = Fintype.card W →
      ∀ (G : SimpleGraph V) (H : SimpleGraph W),
        G.IsTree → H.IsTree →
        (∀ v : V, (G.neighborSet v).ncard ≤ 2) →
        (∀ w : W, (H.neighborSet w).ncard ≤ 2) →
        Nonempty (G ≃g H) := by
  intro V W _ _ hV hVW G H hG hH hdegG hdegH
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Fintype.card V = m + 1 := ⟨Fintype.card V - 1, by omega⟩
  have hmW : Fintype.card W = m + 1 := hVW.symm.trans hm
  have hdegG' : ∀ v : V, G.degree v ≤ 2 := fun v => by
    rw [← ncard_neighborSet_eq_degree]
    exact hdegG v
  have hdegH' : ∀ w : W, H.degree w ≤ 2 := fun w => by
    rw [← ncard_neighborSet_eq_degree]
    exact hdegH w
  obtain ⟨uG, huG⟩ := exists_deg_le_one_of_tree G hG (by omega) hdegG'
  obtain ⟨uH, huH⟩ := exists_deg_le_one_of_tree H hH (by omega) hdegH'
  obtain ⟨φG, _⟩ := path_tree_from_end m G hG hm hdegG' uG huG
  obtain ⟨φH, _⟩ := path_tree_from_end m H hH hmW hdegH' uH huH
  exact ⟨φG.trans φH.symm⟩

end TreeR1H1

theorem OMA.solution : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1.H1 := by
  exact tree_R1_H1
