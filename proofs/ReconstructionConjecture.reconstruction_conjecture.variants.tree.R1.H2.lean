import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1

/-!
# Kelly's Lemma for hypomorphic graphs (`tree.R1.H2` offline pre-proof)

Double-counting occurrences of an induced subgraph isomorphic to `Q` across all vertex-deleted
subgraphs gives `(card V - card U) * s(Q, G) = ∑ v, s(Q, G - v)`, which implies equality when
`G` and `H` are hypomorphic and `card U < card V`.
-/

-- Credit: @green-notes

open SimpleGraph ReconstructionConjecture

section TreeR1H2

open Classical

private noncomputable def subgraphs {V U : Type} [Fintype V] [Fintype U]
    (G : SimpleGraph V) (Q : SimpleGraph U) : Finset (Finset V) :=
  Finset.univ.filter fun S : Finset V => Nonempty (G.induce (S : Set V) ≃g Q)

private lemma ncard_subgraphs_eq {V U : Type} [Fintype V] [Fintype U]
    (G : SimpleGraph V) (Q : SimpleGraph U) :
    {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard = (subgraphs G Q).card := by
  have h : {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)} =
      ((subgraphs G Q : Finset (Finset V)) : Set (Finset V)) := by
    ext S
    simp [subgraphs]
  rw [h, Set.ncard_coe_finset]

private noncomputable def induce_iso_map {A B : Type*} {GA : SimpleGraph A} {GB : SimpleGraph B}
    (φ : GA ≃g GB) (S : Finset A) :
    (GA.induce (S : Set A)) ≃g
      (GB.induce ((S.map φ.toEquiv.toEmbedding : Finset B) : Set B)) where
  toFun x := ⟨φ x.1, Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨x.1, Finset.mem_coe.mp x.2, rfl⟩)⟩
  invFun y :=
    ⟨φ.symm y.1, by
      obtain ⟨a, ha, hfa⟩ := Finset.mem_map.mp (Finset.mem_coe.mp y.2)
      have ha' : φ.symm y.1 = a := by
        have h := congrArg φ.symm hfa
        simpa using h.symm
      rw [Finset.mem_coe, ha']
      exact ha⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply x.1)
  right_inv y := Subtype.ext (φ.apply_symm_apply y.1)
  map_rel_iff' := @fun x₁ x₂ => φ.map_rel_iff

private lemma subgraphs_card_eq_of_iso {A B U : Type} [Fintype A] [Fintype B] [Fintype U]
    {GA : SimpleGraph A} {GB : SimpleGraph B} (φ : GA ≃g GB) (Q : SimpleGraph U) :
    (subgraphs GA Q).card = (subgraphs GB Q).card := by
  refine Finset.card_bij (fun S _ => S.map φ.toEquiv.toEmbedding) ?_ ?_ ?_
  · intro S hS
    simp only [subgraphs, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    obtain ⟨e⟩ := hS
    exact ⟨(induce_iso_map φ S).symm.trans e⟩
  · intro S₁ _ S₂ _ h
    ext a
    have hm := Finset.ext_iff.mp h (φ a)
    simp only [Finset.mem_map, RelIso.coe_fn_toEquiv, Equiv.coe_toEmbedding] at hm
    constructor <;> intro ha
    · obtain ⟨b, hb, hba⟩ := hm.mp ⟨a, ha, rfl⟩
      exact (φ.injective hba) ▸ hb
    · obtain ⟨b, hb, hba⟩ := hm.mpr ⟨a, ha, rfl⟩
      exact (φ.injective hba) ▸ hb
  · intro T hT
    simp only [subgraphs, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    obtain ⟨e⟩ := hT
    refine ⟨T.map φ.symm.toEquiv.toEmbedding, ?_, ?_⟩
    · simp only [subgraphs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(induce_iso_map φ.symm T).symm.trans e⟩
    · ext b
      rw [Finset.mem_map]
      constructor
      · rintro ⟨a, ha, hba⟩
        rw [Finset.mem_map] at ha
        obtain ⟨b', hb', hbb'⟩ := ha
        have heq : b' = b := by
          have h := congrArg φ hbb'
          simpa using h.trans hba
        exact heq ▸ hb'
      · intro hb
        exact ⟨φ.symm b, Finset.mem_map.mpr ⟨b, hb, rfl⟩, by simp⟩

private noncomputable def induce_compl_iso_map {V : Type*} (G : SimpleGraph V) (v : V)
    (T : Finset ({v}ᶜ : Set V)) :
    (G.induce {v}ᶜ).induce (T : Set ({v}ᶜ : Set V)) ≃g
      G.induce ((T.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset V) : Set V) where
  toFun x := ⟨x.1.1, Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨x.1, Finset.mem_coe.mp x.2, rfl⟩)⟩
  invFun y :=
    let hy := Finset.mem_map.mp (Finset.mem_coe.mp y.2)
    ⟨hy.choose, Finset.mem_coe.mpr hy.choose_spec.1⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    have hy := Finset.mem_map.mp (Finset.mem_coe.mp
      (Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨x.1, Finset.mem_coe.mp x.2, rfl⟩) :
        x.1.1 ∈ ((T.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset V) : Set V)))
    exact hy.choose_spec.2
  right_inv y := by
    apply Subtype.ext
    have hy := Finset.mem_map.mp (Finset.mem_coe.mp y.2)
    exact hy.choose_spec.2
  map_rel_iff' := @fun x₁ x₂ => by
    rfl

private lemma induced_count_identity {V U : Type} [Fintype V] [Fintype U]
    (G : SimpleGraph V) (Q : SimpleGraph U) :
    (subgraphs G Q).card * (Fintype.card V - Fintype.card U) =
      ∑ v : V, (subgraphs (G.induce {v}ᶜ) Q).card := by
  have hL : (subgraphs G Q).card * (Fintype.card V - Fintype.card U) =
      ((subgraphs G Q).sigma fun S : Finset V => Sᶜ).card := by
    rw [Finset.card_sigma]
    refine (Finset.sum_const_nat fun S hS => ?_).symm
    simp only [subgraphs, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    obtain ⟨e⟩ := hS
    have hcardS : S.card = Fintype.card U :=
      (Fintype.card_coe S).symm.trans (Fintype.card_congr e.toEquiv)
    rw [Finset.card_compl, hcardS]
  have hR : ∑ v : V, (subgraphs (G.induce {v}ᶜ) Q).card =
      ((Finset.univ : Finset V).sigma fun v : V => subgraphs (G.induce {v}ᶜ) Q).card := by
    rw [Finset.card_sigma]
  rw [hL, hR]
  refine Finset.card_bij
    (fun ⟨S, v⟩ _ => ⟨v, Finset.univ.filter fun x : ({v}ᶜ : Set V) => x.1 ∈ S⟩) ?_ ?_ ?_
  · rintro ⟨S, v⟩ hsv
    simp only [subgraphs, Finset.mem_sigma, Finset.mem_compl, Finset.mem_filter,
      Finset.mem_univ, true_and] at hsv ⊢
    rcases hsv with ⟨⟨e⟩, hvS⟩
    refine ⟨?_⟩
    let T : Finset ({v}ᶜ : Set V) := Finset.univ.filter fun x : ({v}ᶜ : Set V) => x.1 ∈ S
    have hTS : T.map ⟨Subtype.val, Subtype.val_injective⟩ = S := by
      ext y
      simp only [T, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨z, _⟩, hzS, rfl⟩
        exact hzS
      · intro hyS
        have hyv : y ∈ ({v}ᶜ : Set V) := fun h => hvS (h ▸ hyS)
        exact ⟨⟨y, hyv⟩, hyS, rfl⟩
    refine (induce_compl_iso_map G v T).trans ?_
    rw [hTS]
    exact e
  · rintro ⟨S₁, v₁⟩ h1 ⟨S₂, v₂⟩ h2 heq
    rw [Finset.mem_sigma, Finset.mem_compl] at h1 h2
    have hv : v₁ = v₂ := congrArg Sigma.fst heq
    subst hv
    have hT : (Finset.univ.filter fun x : ({v₁}ᶜ : Set V) => x.1 ∈ S₁) =
        Finset.univ.filter fun x : ({v₁}ᶜ : Set V) => x.1 ∈ S₂ :=
      eq_of_heq (Sigma.ext_iff.mp heq).2
    have hS : S₁ = S₂ := by
      ext y
      by_cases hy : y = v₁
      · subst hy
        exact ⟨fun h => False.elim (h1.2 h), fun h => False.elim (h2.2 h)⟩
      · have hm := Finset.ext_iff.mp hT ⟨y, hy⟩
        simpa using hm
    subst hS
    rfl
  · rintro ⟨v, T⟩ hvt
    simp only [subgraphs, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hvt
    obtain ⟨e⟩ := hvt
    let S : Finset V := T.map ⟨Subtype.val, Subtype.val_injective⟩
    have hvS : v ∉ S := by
      intro h
      obtain ⟨⟨x, hx⟩, _, hxv⟩ := Finset.mem_map.mp h
      exact hx (Set.mem_singleton_iff.mpr hxv)
    refine ⟨⟨S, v⟩, ?_, ?_⟩
    · simp only [subgraphs, Finset.mem_sigma, Finset.mem_compl, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨⟨(induce_compl_iso_map G v T).symm.trans e⟩, hvS⟩
    · refine Sigma.ext rfl (heq_of_eq ?_)
      ext ⟨x, hx⟩
      simp [S]

private lemma tree_R1_H2 :
    ∀ {V W : Type} [Fintype V] [Fintype W],
      3 ≤ Fintype.card V →
      ∀ (G : SimpleGraph V) (H : SimpleGraph W),
        G.IsTree → H.IsTree → Hypomorphic G H →
        ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
          Fintype.card U < Fintype.card V →
          {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
            {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard := by
  intro V W _ _ _ G H _ _ hhyp U _ Q hUV
  rw [ncard_subgraphs_eq, ncard_subgraphs_eq]
  have hpos : 0 < Fintype.card V - Fintype.card U := Nat.sub_pos_of_lt hUV
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [induced_count_identity G Q, hhyp.card_eq, induced_count_identity H Q]
  obtain ⟨σ, hσ⟩ := hhyp
  refine Fintype.sum_equiv σ _ _ fun v => ?_
  obtain ⟨φ⟩ := hσ v
  exact subgraphs_card_eq_of_iso φ Q

end TreeR1H2

theorem OMA.solution : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1.H2 := by
  exact tree_R1_H2
