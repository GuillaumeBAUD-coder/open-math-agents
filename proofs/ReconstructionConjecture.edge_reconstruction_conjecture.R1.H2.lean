import OMAReductions.R_ReconstructionConjecture_edge_reconstruction_conjecture_R1

/-!
Step `ReconstructionConjecture.edge_reconstruction_conjecture.R1.H2`:
Müller (1977) theorem (`n! < 2 ^ (m - 1)` implies edge-reconstructibility).
-/

-- Step ReconstructionConjecture.edge_reconstruction_conjecture.R1.H2: hypothesis H2
-- Credit: @green-notes

open ReconstructionConjecture SimpleGraph Finset

private def permMap {V : Type*} (σ : Equiv.Perm V) (e : Sym2 V) : Sym2 V :=
  Sym2.map σ e

private lemma permMap_inj {V : Type*} (σ : Equiv.Perm V) :
    Function.Injective (permMap σ) := by
  intro x y hxy
  have h : Sym2.map σ.symm (Sym2.map σ x) = Sym2.map σ.symm (Sym2.map σ y) := by
    dsimp [permMap] at hxy
    rw [hxy]
  simpa [Sym2.map_map] using h

private lemma edgeFinset_erase_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    [DecidableRel (G.deleteEdges ({e} : Set (Sym2 V))).Adj] :
    (G.deleteEdges ({e} : Set (Sym2 V))).edgeFinset = G.edgeFinset.erase e := by
  ext x
  induction x using Sym2.ind with
  | h u v =>
    simp only [mem_edgeFinset, mem_edgeSet, deleteEdges_adj, Set.mem_singleton_iff,
      mem_erase, ne_eq]
    tauto

private lemma count_pairs_double {V : Type*} [Fintype V] [DecidableEq V]
    (T Y : Finset (Sym2 V)) (_hYT : Y.card ≤ T.card) :
    ∑ e ∈ T, ((Finset.univ : Finset (Equiv.Perm V)).filter
        (fun σ : Equiv.Perm V => ∀ y ∈ Y, permMap σ y ∈ T.erase e)).card =
      (T.card - Y.card) * ((Finset.univ : Finset (Equiv.Perm V)).filter
        (fun σ : Equiv.Perm V => ∀ y ∈ Y, permMap σ y ∈ T)).card := by
  classical
  have h1 :
      ∑ e ∈ T, ((Finset.univ : Finset (Equiv.Perm V)).filter
          (fun σ : Equiv.Perm V => ∀ y ∈ Y, permMap σ y ∈ T.erase e)).card =
        ∑ e ∈ T, ∑ σ : Equiv.Perm V,
          if (∀ y ∈ Y, permMap σ y ∈ T) ∧ e ∉ Y.image (permMap σ) then (1 : ℕ) else 0 := by
    refine sum_congr rfl fun e _ => ?_
    rw [card_filter]
    refine sum_congr rfl fun σ _ => ?_
    congr 1
    apply propext
    constructor
    · intro h
      refine ⟨fun y hy => (mem_erase.mp (h y hy)).2, ?_⟩
      intro he
      obtain ⟨y, hy, rfl⟩ := mem_image.mp he
      exact (mem_erase.mp (h y hy)).1 rfl
    · rintro ⟨hT, he⟩ y hy
      refine mem_erase.mpr ⟨?_, hT y hy⟩
      intro hye
      exact he (mem_image.mpr ⟨y, hy, hye⟩)
  rw [h1, sum_comm]
  have h2 :
      ∑ σ : Equiv.Perm V, ∑ e ∈ T,
          (if (∀ y ∈ Y, permMap σ y ∈ T) ∧ e ∉ Y.image (permMap σ) then (1 : ℕ) else 0) =
        ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm V)).filter
            (fun σ : Equiv.Perm V => ∀ y ∈ Y, permMap σ y ∈ T),
          (T.card - Y.card) := by
    rw [sum_filter]
    refine sum_congr rfl fun σ _ => ?_
    by_cases hσ : ∀ y ∈ Y, permMap σ y ∈ T
    · have h_lhs : ∀ e ∈ T,
          (if (∀ y ∈ Y, permMap σ y ∈ T) ∧ e ∉ Y.image (permMap σ) then (1 : ℕ) else 0) =
          (if e ∉ Y.image (permMap σ) then 1 else 0) :=
        fun e _ => if_congr (and_iff_right hσ) rfl rfl
      rw [sum_congr rfl h_lhs, if_pos hσ]
      have hsub : Y.image (permMap σ) ⊆ T := by
        intro z hz
        obtain ⟨y, hy, rfl⟩ := mem_image.mp hz
        exact hσ y hy
      have hcard : (Y.image (permMap σ)).card = Y.card :=
        card_image_of_injective Y (permMap_inj σ)
      have hsdiff : (T \ Y.image (permMap σ)).card = T.card - Y.card := by
        rw [card_sdiff_of_subset hsub, hcard]
      rw [← hsdiff, card_eq_sum_ones, ← sum_filter]
      refine sum_congr (by ext e; simp only [mem_filter, mem_sdiff]) fun _ _ => rfl
    · have h_lhs : ∀ e ∈ T,
          (if (∀ y ∈ Y, permMap σ y ∈ T) ∧ e ∉ Y.image (permMap σ) then (1 : ℕ) else 0) = 0 :=
        fun e _ => by simp only [hσ, false_and, ↓reduceIte]
      rw [sum_congr rfl h_lhs, sum_const_zero, if_neg hσ]
  rw [h2, sum_const, smul_eq_mul, mul_comm]

private lemma sum_powerset_neg_one {α : Type*} [DecidableEq α] (T : Finset α) :
    ∑ Z ∈ T.powerset, (-1 : ℤ) ^ Z.card = if T = ∅ then 1 else 0 := by
  induction T using Finset.induction with
  | empty => simp
  | @insert a T haT ih =>
    have hne : insert a T ≠ ∅ := insert_ne_empty a T
    rw [if_neg hne, powerset_insert]
    have hdisj : Disjoint T.powerset (T.powerset.image (insert a)) := by
      rw [Finset.disjoint_left]
      intro Z hZT hZi
      obtain ⟨W, _, rfl⟩ := mem_image.mp hZi
      have haW : a ∈ insert a W := mem_insert_self a W
      exact haT (mem_powerset.mp hZT haW)
    have hinj : Set.InjOn (insert a) (T.powerset : Set (Finset α)) := by
      intro W₁ hW₁ W₂ hW₂ heq
      have ha₁ : a ∉ W₁ := fun h => haT (mem_powerset.mp hW₁ h)
      have ha₂ : a ∉ W₂ := fun h => haT (mem_powerset.mp hW₂ h)
      ext x
      have hx := congrArg (fun S : Finset α => x ∈ S) heq
      simp only [mem_insert] at hx
      by_cases hxa : x = a
      · subst hxa; exact iff_of_false ha₁ ha₂
      · simpa [hxa] using hx
    rw [sum_union hdisj, sum_image (fun W₁ h₁ W₂ h₂ h => hinj h₁ h₂ h)]
    have hsum_neg : ∑ Z ∈ T.powerset, (-1 : ℤ) ^ (insert a Z).card =
        - ∑ Z ∈ T.powerset, (-1 : ℤ) ^ Z.card := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun Z hZ => ?_
      have haZ : a ∉ Z := fun h => haT (mem_powerset.mp hZ h)
      rw [card_insert_of_notMem haZ, pow_succ]
      ring
    rw [hsum_neg, add_neg_cancel]

private lemma sum_inclusion_exclusion {V : Type*} [Fintype V] [DecidableEq V]
    (E T X : Finset (Sym2 V)) (hXE : X ⊆ E) :
    ∑ Y ∈ E.powerset.filter (X ⊆ ·), (-1 : ℤ) ^ (Y.card - X.card) *
        (((Finset.univ : Finset (Equiv.Perm V)).filter
          (fun σ : Equiv.Perm V => ∀ y ∈ Y, permMap σ y ∈ T)).card : ℤ) =
      (((Finset.univ : Finset (Equiv.Perm V)).filter
        (fun σ : Equiv.Perm V => E.filter (fun e => permMap σ e ∈ T) = X)).card : ℤ) := by
  classical
  have h1 :
      ∑ Y ∈ E.powerset.filter (X ⊆ ·), (-1 : ℤ) ^ (Y.card - X.card) *
          (((Finset.univ : Finset (Equiv.Perm V)).filter
            (fun σ : Equiv.Perm V => ∀ y ∈ Y, permMap σ y ∈ T)).card : ℤ) =
        ∑ Y ∈ E.powerset.filter (X ⊆ ·), ∑ σ : Equiv.Perm V,
          if ∀ y ∈ Y, permMap σ y ∈ T then (-1 : ℤ) ^ (Y.card - X.card) else 0 := by
    refine sum_congr rfl fun Y _ => ?_
    rw [card_filter, Nat.cast_sum, mul_sum]
    refine sum_congr rfl fun σ _ => ?_
    split_ifs <;> simp
  rw [h1, sum_comm]
  have h2 :
      ∑ σ : Equiv.Perm V, ∑ Y ∈ E.powerset.filter (X ⊆ ·),
          (if ∀ y ∈ Y, permMap σ y ∈ T then (-1 : ℤ) ^ (Y.card - X.card) else 0) =
        ∑ σ : Equiv.Perm V,
          if E.filter (fun e => permMap σ e ∈ T) = X then (1 : ℤ) else 0 := by
    refine sum_congr rfl fun σ _ => ?_
    let S := E.filter (fun e => permMap σ e ∈ T)
    have hSE : S ⊆ E := filter_subset _ _
    have hinner :
        ∑ Y ∈ E.powerset.filter (X ⊆ ·),
            (if ∀ y ∈ Y, permMap σ y ∈ T then (-1 : ℤ) ^ (Y.card - X.card) else 0) =
          ∑ Y ∈ (E.powerset.filter (X ⊆ ·)).filter (· ⊆ S), (-1 : ℤ) ^ (Y.card - X.card) := by
      conv_rhs => rw [sum_filter]
      refine sum_congr rfl fun Y hY => ?_
      have hYE : Y ⊆ E := mem_powerset.mp (mem_filter.mp hY).1
      have hiff : (∀ y ∈ Y, permMap σ y ∈ T) ↔ Y ⊆ S := by
        constructor
        · intro hy y hyY
          exact mem_filter.mpr ⟨hYE hyY, hy y hyY⟩
        · intro hYS y hyY
          exact (mem_filter.mp (hYS hyY)).2
      rw [if_congr hiff rfl rfl]
    rw [hinner]
    by_cases hXS : X ⊆ S
    · have himg : (E.powerset.filter (X ⊆ ·)).filter (· ⊆ S) =
          (S \ X).powerset.image (fun Z => X ∪ Z) := by
        ext Y
        simp only [mem_filter, mem_powerset, mem_image]
        constructor
        · rintro ⟨⟨hYE, hXY⟩, hYS⟩
          refine ⟨Y \ X, fun z hz => ?_, union_sdiff_of_subset hXY⟩
          exact mem_sdiff.mpr ⟨hYS (mem_sdiff.mp hz).1, (mem_sdiff.mp hz).2⟩
        · rintro ⟨Z, hZSX, rfl⟩
          refine ⟨⟨union_subset hXE (hZSX.trans (sdiff_subset.trans hSE)), subset_union_left⟩,
            union_subset hXS (hZSX.trans sdiff_subset)⟩
      have hinj : Set.InjOn (fun Z => X ∪ Z) ((S \ X).powerset : Set (Finset (Sym2 V))) := by
        intro Z₁ hZ₁ Z₂ hZ₂ heq
        have hd₁ : Disjoint X Z₁ := disjoint_sdiff_self_right.mono_right (mem_powerset.mp hZ₁)
        have hd₂ : Disjoint X Z₂ := disjoint_sdiff_self_right.mono_right (mem_powerset.mp hZ₂)
        ext x
        have hx := congrArg (fun W : Finset (Sym2 V) => x ∈ W) heq
        simp only [mem_union] at hx
        by_cases hxX : x ∈ X
        · exact iff_of_false (Finset.disjoint_left.mp hd₁ hxX) (Finset.disjoint_left.mp hd₂ hxX)
        · simpa [hxX] using hx
      rw [himg, sum_image (fun Z₁ h₁ Z₂ h₂ h => hinj h₁ h₂ h)]
      have hcard_eq : ∀ Z ∈ (S \ X).powerset, (X ∪ Z).card - X.card = Z.card := by
        intro Z hZ
        have hd : Disjoint X Z := disjoint_sdiff_self_right.mono_right (mem_powerset.mp hZ)
        rw [card_union_of_disjoint hd]
        omega
      have hsum_eq : ∑ Z ∈ (S \ X).powerset, (-1 : ℤ) ^ ((X ∪ Z).card - X.card) =
          ∑ Z ∈ (S \ X).powerset, (-1 : ℤ) ^ Z.card :=
        sum_congr rfl fun Z hZ => by rw [hcard_eq Z hZ]
      rw [hsum_eq, sum_powerset_neg_one]
      have hsdiff_empty : S \ X = ∅ ↔ S = X := by
        rw [sdiff_eq_empty_iff_subset]
        exact ⟨fun hSX => Subset.antisymm hSX hXS, fun h => h.le⟩
      rw [if_congr hsdiff_empty rfl rfl]
    · have hempty : (E.powerset.filter (X ⊆ ·)).filter (· ⊆ S) = ∅ := by
        ext Y
        simp only [mem_filter, mem_powerset, notMem_empty, iff_false]
        rintro ⟨⟨_, hXY⟩, hYS⟩
        exact hXS (hXY.trans hYS)
      have hne : S ≠ X := fun h => hXS (h ▸ Subset.rfl)
      rw [hempty, sum_empty, if_neg hne]
  rw [h2, card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

private lemma odd_powerset_card {α : Type*} [DecidableEq α] (E : Finset α) (hE : 1 ≤ E.card) :
    (E.powerset.filter (fun X => Odd (E.card - X.card))).card = 2 ^ (E.card - 1) := by
  have hne : E.Nonempty := card_pos.mp (by omega)
  obtain ⟨e₀, he₀⟩ := hne
  let OddS := E.powerset.filter (fun X => Odd (E.card - X.card))
  let EvenS := E.powerset.filter (fun X => ¬ Odd (E.card - X.card))
  let toggle : Finset α → Finset α := fun X => if e₀ ∈ X then X.erase e₀ else insert e₀ X
  have htoggle_mem : ∀ X ∈ E.powerset, toggle X ∈ E.powerset := by
    intro X hX
    rw [mem_powerset] at hX ⊢
    dsimp [toggle]
    split_ifs
    · exact (erase_subset _ _).trans hX
    · exact insert_subset_iff.mpr ⟨he₀, hX⟩
  have hparity : ∀ X ∈ E.powerset, (Odd (E.card - (toggle X).card) ↔ ¬ Odd (E.card - X.card)) := by
    intro X hX
    have hXcard : X.card ≤ E.card := card_le_card (mem_powerset.mp hX)
    dsimp [toggle]
    split_ifs with h
    · have hc : (X.erase e₀).card + 1 = X.card := card_erase_add_one h
      have hdiff : E.card - (X.erase e₀).card = (E.card - X.card) + 1 := by omega
      rw [hdiff, Nat.odd_add_one]
    · have hc : (insert e₀ X).card = X.card + 1 := card_insert_of_notMem h
      have hmem_ins : insert e₀ X ∈ E.powerset := by
        simpa [toggle, h] using htoggle_mem X hX
      have hXc1 : X.card + 1 ≤ E.card := by
        rw [← hc]
        exact card_le_card (mem_powerset.mp hmem_ins)
      have hdiff : E.card - X.card = (E.card - (insert e₀ X).card) + 1 := by omega
      rw [hdiff, Nat.odd_add_one, not_not]
  have htoggle_inv : ∀ X : Finset α, toggle (toggle X) = X := by
    intro X
    dsimp [toggle]
    split_ifs with h1 h2 h2
    · exfalso; exact (mem_erase.mp h2).1 rfl
    · exact insert_erase h1
    · exact erase_insert h1
    · exfalso; exact h2 (mem_insert_self e₀ X)
  have hbij : OddS.card = EvenS.card := by
    refine Finset.card_bij (fun X _ => toggle X) ?_ ?_ ?_
    · intro X hX
      obtain ⟨hXp, hXo⟩ := mem_filter.mp hX
      exact mem_filter.mpr ⟨htoggle_mem X hXp, fun hc => (hparity X hXp).mp hc hXo⟩
    · intro X₁ _ X₂ _ heq
      calc X₁ = toggle (toggle X₁) := (htoggle_inv X₁).symm
        _ = toggle (toggle X₂) := by rw [heq]
        _ = X₂ := htoggle_inv X₂
    · intro Y hY
      obtain ⟨hYp, hYo⟩ := mem_filter.mp hY
      exact ⟨toggle Y, mem_filter.mpr ⟨htoggle_mem Y hYp, (hparity Y hYp).mpr hYo⟩, htoggle_inv Y⟩
  have hsum : OddS.card + EvenS.card = E.powerset.card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext X
      simp only [OddS, EvenS, mem_union, mem_filter]
      tauto
    · rw [Finset.disjoint_left]
      intro X h1 h2
      exact (mem_filter.mp h2).2 (mem_filter.mp h1).2
  rw [hbij, card_powerset] at hsum
  have hpow : 2 ^ E.card = 2 * 2 ^ (E.card - 1) := by
    conv_lhs => rw [show E.card = (E.card - 1) + 1 by omega, pow_succ']
  change OddS.card = 2 ^ (E.card - 1)
  omega

theorem OMA.solution : OMA.R_ReconstructionConjecture_edge_reconstruction_conjecture_R1.H2 := by
  intro V _ G H hV hm hfact hconn hiso hed hhyp
  classical
  by_contra hnot
  let E := G.edgeFinset
  let EH := H.edgeFinset
  have hE_ncard : E.card = G.edgeSet.ncard := by
    simpa [E] using (Set.ncard_coe_finset G.edgeFinset).symm.trans (by
      congr 1
      exact G.coe_edgeFinset)
  have hmE : 4 ≤ E.card := by omega
  obtain ⟨φ, hφ⟩ := hed
  have hE_eq_EH : E.card = EH.card := by
    have h1 : E.card = Fintype.card G.edgeSet := by
      rw [show E = Finset.univ.filter (fun e => e ∈ G.edgeSet) by
        ext e; simp [E, mem_edgeFinset], ← Fintype.card_subtype]
    have h2 : EH.card = Fintype.card H.edgeSet := by
      rw [show EH = Finset.univ.filter (fun e => e ∈ H.edgeSet) by
        ext e; simp [EH, mem_edgeFinset], ← Fintype.card_subtype]
    rw [h1, h2]
    exact Fintype.card_congr φ
  have hkelly : ∀ Y ⊆ E, Y ≠ E →
      ((Finset.univ : Finset (Equiv.Perm V)).filter
          (fun σ : Equiv.Perm V => ∀ y ∈ Y, permMap σ y ∈ E)).card =
        ((Finset.univ : Finset (Equiv.Perm V)).filter
          (fun σ : Equiv.Perm V => ∀ y ∈ Y, permMap σ y ∈ EH)).card := by
    intro Y hYE hYne
    have hY_lt : Y.card < E.card := by
      have hle := card_le_card hYE
      by_contra hge
      have hcard : Y.card = E.card := by omega
      exact hYne (eq_of_subset_of_card_le hYE hcard.ge)
    have hY_le_EH : Y.card ≤ EH.card := by omega
    have hG_double := count_pairs_double E Y (card_le_card hYE)
    have hH_double := count_pairs_double EH Y hY_le_EH
    have hsum_eq :
        ∑ e ∈ E, ((Finset.univ : Finset (Equiv.Perm V)).filter
            (fun σ : Equiv.Perm V => ∀ y ∈ Y, permMap σ y ∈ E.erase e)).card =
          ∑ e' ∈ EH, ((Finset.univ : Finset (Equiv.Perm V)).filter
            (fun σ : Equiv.Perm V => ∀ y ∈ Y, permMap σ y ∈ EH.erase e')).card := by
      refine Finset.sum_bij (fun e he => (φ ⟨e, mem_edgeFinset.mp he⟩ : Sym2 V)) ?_ ?_ ?_ ?_
      · intro e he
        exact mem_edgeFinset.mpr (φ ⟨e, mem_edgeFinset.mp he⟩).2
      · intro e₁ he₁ e₂ he₂ heq
        exact congrArg Subtype.val (φ.injective (Subtype.ext heq))
      · intro e' he'
        let pre := φ.symm ⟨e', mem_edgeFinset.mp he'⟩
        refine ⟨pre.1, mem_edgeFinset.mpr pre.2, ?_⟩
        simp [pre]
      · intro e he
        obtain ⟨ψ⟩ := hφ ⟨e, mem_edgeFinset.mp he⟩
        let e' : Sym2 V := (φ ⟨e, mem_edgeFinset.mp he⟩ : Sym2 V)
        change ((Finset.univ : Finset (Equiv.Perm V)).filter
            (fun σ : Equiv.Perm V => ∀ y ∈ Y, permMap σ y ∈ E.erase e)).card =
          ((Finset.univ : Finset (Equiv.Perm V)).filter
            (fun σ : Equiv.Perm V => ∀ y ∈ Y, permMap σ y ∈ EH.erase e')).card
        refine card_bij (fun σ _ => σ.trans ψ.toEquiv) ?_ ?_ ?_
        · intro σ hσ
          simp only [mem_filter, mem_univ, true_and] at hσ ⊢
          intro y hy
          have hyG : permMap σ y ∈ (G.deleteEdges ({e} : Set (Sym2 V))).edgeFinset := by
            rw [edgeFinset_erase_eq]
            exact hσ y hy
          have hyH : Sym2.map ψ.toEquiv (permMap σ y) ∈
              (H.deleteEdges ({e'} : Set (Sym2 V))).edgeFinset := by
            generalize hz : permMap σ y = z at hyG ⊢
            induction z using Sym2.ind with
            | h u v =>
              simp only [Sym2.map_mk, mem_edgeFinset, mem_edgeSet] at hyG ⊢
              exact ψ.map_rel_iff.mpr hyG
          rw [edgeFinset_erase_eq] at hyH
          have heq_map : permMap (σ.trans ψ.toEquiv) y = Sym2.map ψ.toEquiv (permMap σ y) := by
            dsimp [permMap]
            rw [← Sym2.map_map]
          rwa [heq_map]
        · intro σ₁ _ σ₂ _ hcomp
          ext v
          exact ψ.toEquiv.injective (congrArg (fun τ : Equiv.Perm V => τ v) hcomp)
        · intro τ hτ
          simp only [mem_filter, mem_univ, true_and] at hτ
          refine ⟨τ.trans ψ.toEquiv.symm, mem_filter.mpr ⟨mem_univ _, fun y hy => ?_⟩, ?_⟩
          · have hyH : permMap τ y ∈ (H.deleteEdges ({e'} : Set (Sym2 V))).edgeFinset := by
              rw [edgeFinset_erase_eq]
              exact hτ y hy
            have hyG : Sym2.map ψ.symm.toEquiv (permMap τ y) ∈
                (G.deleteEdges ({e} : Set (Sym2 V))).edgeFinset := by
              generalize hz : permMap τ y = z at hyH ⊢
              induction z using Sym2.ind with
              | h u v =>
                simp only [Sym2.map_mk, mem_edgeFinset, mem_edgeSet] at hyH ⊢
                exact ψ.symm.map_rel_iff.mpr hyH
            rw [edgeFinset_erase_eq] at hyG
            have heq_map : permMap (τ.trans ψ.toEquiv.symm) y =
                Sym2.map ψ.symm.toEquiv (permMap τ y) := by
              dsimp [permMap]
              rw [← Sym2.map_map]
              rfl
            rwa [heq_map]
          · ext v
            simp
    rw [hsum_eq, hH_double, ← hE_eq_EH] at hG_double
    have hpos : 0 < E.card - Y.card := by omega
    exact Nat.mul_left_cancel hpos hG_double.symm
  have hAE_pos : 1 ≤ ((Finset.univ : Finset (Equiv.Perm V)).filter
      (fun σ : Equiv.Perm V => ∀ y ∈ E, permMap σ y ∈ E)).card := by
    refine card_pos.mpr ⟨(1 : Equiv.Perm V), mem_filter.mpr ⟨mem_univ _, fun y hy => ?_⟩⟩
    simpa [permMap] using hy
  have hBE_zero : ((Finset.univ : Finset (Equiv.Perm V)).filter
      (fun σ : Equiv.Perm V => ∀ y ∈ E, permMap σ y ∈ EH)).card = 0 := by
    by_contra hnz
    obtain ⟨σ, hσ⟩ := card_pos.mp (Nat.pos_of_ne_zero hnz)
    have hσE : ∀ y ∈ E, permMap σ y ∈ EH := (mem_filter.mp hσ).2
    have himg_sub : E.image (permMap σ) ⊆ EH := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hz
      exact hσE y hy
    have himg_card : (E.image (permMap σ)).card = EH.card := by
      rw [card_image_of_injective E (permMap_inj σ), hE_eq_EH]
    have himg_eq : E.image (permMap σ) = EH := eq_of_subset_of_card_le himg_sub himg_card.ge
    apply hnot
    refine ⟨⟨σ, ?_⟩⟩
    intro u v
    constructor
    · intro huv
      have h1 : s(σ u, σ v) ∈ EH := mem_edgeFinset.mpr ((mem_edgeSet H).mpr huv)
      rw [← himg_eq] at h1
      obtain ⟨y, hy, hy_eq⟩ := mem_image.mp h1
      have hsame : y = s(u, v) := permMap_inj σ (by simpa [permMap, Sym2.map_mk] using hy_eq)
      rw [hsame] at hy
      exact (mem_edgeSet G).mp (mem_edgeFinset.mp hy)
    · intro huv
      have h1 : s(u, v) ∈ E := mem_edgeFinset.mpr ((mem_edgeSet G).mpr huv)
      have h2 : permMap σ s(u, v) ∈ EH := hσE _ h1
      simpa [EH, permMap, Sym2.map_mk, mem_edgeFinset, mem_edgeSet] using h2
  let hitsH : Equiv.Perm V → Finset (Sym2 V) := fun σ => E.filter (fun e => permMap σ e ∈ EH)
  let OddS := E.powerset.filter (fun X => Odd (E.card - X.card))
  have hOdd_sub : OddS ⊆ (Finset.univ : Finset (Equiv.Perm V)).image hitsH := by
    intro X hX
    have hXp := (mem_filter.mp hX).1
    have hXE : X ⊆ E := mem_powerset.mp hXp
    have hXodd : Odd (E.card - X.card) := (mem_filter.mp hX).2
    have hIE_G := sum_inclusion_exclusion E E X hXE
    have hIE_H := sum_inclusion_exclusion E EH X hXE
    have hdiff :
        (((Finset.univ : Finset (Equiv.Perm V)).filter
            (fun σ : Equiv.Perm V => E.filter (fun e => permMap σ e ∈ E) = X)).card : ℤ) -
          (((Finset.univ : Finset (Equiv.Perm V)).filter (fun σ : Equiv.Perm V => hitsH σ = X)).card : ℤ) =
          (-1 : ℤ) ^ (E.card - X.card) *
            (((Finset.univ : Finset (Equiv.Perm V)).filter
              (fun σ : Equiv.Perm V => ∀ y ∈ E, permMap σ y ∈ E)).card : ℤ) := by
      rw [← hIE_G, ← hIE_H, ← sum_sub_distrib]
      have hE_mem : E ∈ E.powerset.filter (X ⊆ ·) := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, hXE⟩
      rw [← insert_erase hE_mem, sum_insert (notMem_erase _ _)]
      have hrest :
          ∑ Y ∈ (E.powerset.filter (X ⊆ ·)).erase E,
              ((-1 : ℤ) ^ (Y.card - X.card) *
                  (((Finset.univ : Finset (Equiv.Perm V)).filter
                    (fun σ : Equiv.Perm V => ∀ y ∈ Y, permMap σ y ∈ E)).card : ℤ) -
                (-1 : ℤ) ^ (Y.card - X.card) *
                  (((Finset.univ : Finset (Equiv.Perm V)).filter
                    (fun σ : Equiv.Perm V => ∀ y ∈ Y, permMap σ y ∈ EH)).card : ℤ)) = 0 := by
        refine sum_eq_zero fun Y hY => ?_
        have hYne : Y ≠ E := (mem_erase.mp hY).1
        have hYE : Y ⊆ E := mem_powerset.mp (mem_filter.mp (mem_erase.mp hY).2).1
        rw [hkelly Y hYE hYne, sub_self]
      rw [hrest, add_zero, hBE_zero]
      simp [sub_zero]
    rw [hXodd.neg_one_pow, neg_one_mul] at hdiff
    have hAE_Z : (1 : ℤ) ≤ (((Finset.univ : Finset (Equiv.Perm V)).filter
        (fun σ : Equiv.Perm V => ∀ y ∈ E, permMap σ y ∈ E)).card : ℤ) := by exact_mod_cast hAE_pos
    have hH_pos : 0 < ((Finset.univ : Finset (Equiv.Perm V)).filter
        (fun σ : Equiv.Perm V => hitsH σ = X)).card := by
      have hg_nn : (0 : ℤ) ≤ (((Finset.univ : Finset (Equiv.Perm V)).filter
          (fun σ : Equiv.Perm V => E.filter (fun e => permMap σ e ∈ E) = X)).card : ℤ) :=
        Int.natCast_nonneg _
      have hh_pos : (0 : ℤ) < (((Finset.univ : Finset (Equiv.Perm V)).filter
          (fun σ : Equiv.Perm V => hitsH σ = X)).card : ℤ) := by linarith
      exact_mod_cast hh_pos
    obtain ⟨σ, hσ⟩ := card_pos.mp hH_pos
    exact mem_image.mpr ⟨σ, mem_univ _, (mem_filter.mp hσ).2⟩
  have hcard_le : 2 ^ (E.card - 1) ≤ Nat.factorial (Fintype.card V) := by
    calc 2 ^ (E.card - 1) = OddS.card := (odd_powerset_card E (by omega)).symm
      _ ≤ ((Finset.univ : Finset (Equiv.Perm V)).image hitsH).card := card_le_card hOdd_sub
      _ ≤ (Finset.univ : Finset (Equiv.Perm V)).card := card_image_le
      _ = Fintype.card (Equiv.Perm V) := card_univ
      _ = Nat.factorial (Fintype.card V) := Fintype.card_perm
  rw [hE_ncard] at hcard_le
  omega
