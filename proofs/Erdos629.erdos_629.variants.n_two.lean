import FormalConjectures.ErdosProblems.«629»

/-! The four assignments from disjoint lists on the smaller side cannot all be blocked. -/

open SimpleGraph

lemma OMA.list_choosable_mono {V : Type*} {G : SimpleGraph V} {k l : ℕ}
    (hkl : k ≤ l) (hk : G.IsKChoosable k) : G.IsKChoosable l := by
  intro L hL
  have hex (v : V) : ∃ M ⊆ L v, (M : Finset ℕ).card = k :=
    Finset.exists_subset_card_eq (by rw [hL]; exact hkl)
  choose M hM_sub hM_card using hex
  obtain ⟨C, hC⟩ := hk M hM_card
  exact ⟨C, fun v => hM_sub v (hC v)⟩

lemma OMA.list_choosable_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
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

lemma OMA.two_list_color_from_palette {V : Type*} (G : SimpleGraph V) (A : Finset V)
    (L : V → Finset ℕ) (palette : Finset ℕ) (left : V → ℕ)
    (hcross : ∀ {v w}, G.Adj v w → (v ∈ A ↔ w ∉ A))
    (hleft_list : ∀ v ∈ A, left v ∈ L v) (hleft_palette : ∀ v ∈ A, left v ∈ palette)
    (hright : ∀ v ∉ A, ¬ L v ⊆ palette) :
    ∃ C : G.Coloring ℕ, ∀ v, C v ∈ L v := by
  classical
  have hex (v : V) (hv : v ∉ A) : ∃ c ∈ L v, c ∉ palette :=
    Finset.not_subset.mp (hright v hv)
  let right (v : V) (hv : v ∉ A) : ℕ := (hex v hv).choose
  have hright_list (v : V) (hv : v ∉ A) : right v hv ∈ L v := (hex v hv).choose_spec.1
  have hright_palette (v : V) (hv : v ∉ A) : right v hv ∉ palette := (hex v hv).choose_spec.2
  let color (v : V) : ℕ := if h : v ∈ A then left v else right v h
  refine ⟨Coloring.mk color ?_, ?_⟩
  · intro v w hAdj hEq
    by_cases hv : v ∈ A
    · have hw := (hcross hAdj).mp hv
      have heq : left v = right w hw := by simpa [color, hv, hw] using hEq
      exact hright_palette w hw (heq ▸ hleft_palette v hv)
    · have hw : w ∈ A := by
        by_contra h
        exact hv ((hcross hAdj).mpr h)
      have heq : right v hv = left w := by simpa [color, hv, hw] using hEq
      exact hright_palette v hv (heq.symm ▸ hleft_palette w hw)
  · intro v
    by_cases hv : v ∈ A
    · simpa [Coloring.mk, color, hv] using hleft_list v hv
    · simpa [Coloring.mk, color, hv] using hright_list v hv

lemma OMA.two_list_pair_injective (P Q : Finset ℕ) (hD : Disjoint P Q) :
    Set.InjOn (fun ab : ℕ × ℕ => ({ab.1, ab.2} : Finset ℕ)) (↑(P ×ˢ Q)) := by
  intro ab hab cd hcd hEq
  change ({ab.1, ab.2} : Finset ℕ) = {cd.1, cd.2} at hEq
  have hab_mem := Finset.mem_product.mp hab
  have hcd_mem := Finset.mem_product.mp hcd
  have hdisj := Finset.disjoint_left.mp hD
  have hfirst : ab.1 ∈ ({cd.1, cd.2} : Finset ℕ) := by rw [← hEq]; simp
  have hsecond : ab.2 ∈ ({cd.1, cd.2} : Finset ℕ) := by rw [← hEq]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
  apply Prod.ext
  · exact hfirst.resolve_right (fun h => hdisj hab_mem.1 (h.symm ▸ hcd_mem.2))
  · exact hsecond.resolve_left (fun h => hdisj (h.symm ▸ hcd_mem.1) hab_mem.2)

lemma OMA.two_list_good_pair {V : Type*} (R : Finset V) (L : V → Finset ℕ)
    (hR : R.card ≤ 3) (P Q : Finset ℕ) (hP : P.card = 2) (hQ : Q.card = 2)
    (hD : Disjoint P Q) :
    ∃ ab ∈ P ×ˢ Q, ∀ v ∈ R, L v ≠ ({ab.1, ab.2} : Finset ℕ) := by
  classical
  by_contra h
  have hblocked (ab : ↥(P ×ˢ Q)) : ∃ v ∈ R, L v = ({ab.val.1, ab.val.2} : Finset ℕ) := by
    by_contra hc
    push Not at hc
    exact h ⟨ab.val, ab.property, hc⟩
  choose f hf_mem hf_eq using hblocked
  let g (ab : ↥(P ×ˢ Q)) : ↥R := ⟨f ab, hf_mem ab⟩
  have hg : Function.Injective g := by
    intro ab cd heq
    have hEq : f ab = f cd := congrArg Subtype.val heq
    apply Subtype.ext
    apply OMA.two_list_pair_injective P Q hD ab.property cd.property
    change ({ab.val.1, ab.val.2} : Finset ℕ) = {cd.val.1, cd.val.2}
    rw [← hf_eq ab, ← hf_eq cd, hEq]
  have hle := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_coe, Finset.card_product, hP, hQ] at hle
  omega

lemma OMA.two_list_small_side (m : ℕ) (hm : m ≤ 5) (G : SimpleGraph (Fin m))
    (A : Finset (Fin m)) (hA : A.card ≤ 2)
    (hcross : ∀ {v w}, G.Adj v w → (v ∈ A ↔ w ∉ A)) :
    G.IsKChoosable 2 := by
  classical
  intro L hL
  have avoid_small (palette : Finset ℕ) (hs : palette.card ≤ 1) (v : Fin m) :
      ¬ L v ⊆ palette := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [hL v] at hle
    omega
  by_cases hs : A.card ≤ 1
  · have hex (v : Fin m) : ∃ c, c ∈ L v := Finset.card_pos.mp (by rw [hL]; decide)
    choose left hleft using hex
    have hsmall : (A.image left).card ≤ 1 := Finset.card_image_le.trans hs
    exact OMA.two_list_color_from_palette G A L (A.image left) left hcross
      (fun v _ => hleft v) (fun _ hv => Finset.mem_image_of_mem left hv)
      (fun v _ => avoid_small _ hsmall v)
  · have hA_two : A.card = 2 := by omega
    obtain ⟨a, b, hab, hAb⟩ := Finset.card_eq_two.mp hA_two
    by_cases hinter : (L a ∩ L b).Nonempty
    · obtain ⟨c, hc⟩ := hinter
      obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hc
      apply OMA.two_list_color_from_palette G A L {c} (fun _ => c) hcross
      · intro v hv
        rw [hAb] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact ha
        · exact hb
      · exact fun _ _ => Finset.mem_singleton_self c
      · exact fun v _ => avoid_small _ (by simp) v
    · have hdisj : Disjoint (L a) (L b) := by
        apply Finset.disjoint_left.mpr
        intro c hca hcb
        exact hinter ⟨c, Finset.mem_inter.mpr ⟨hca, hcb⟩⟩
      let R := Finset.univ \ A
      have hR : R.card ≤ 3 := by
        dsimp [R]
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hA_two,
          Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨⟨x, y⟩, hxy, hgood⟩ := OMA.two_list_good_pair R L hR (L a) (L b)
        (hL a) (hL b) hdisj
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
      let left (v : Fin m) : ℕ := if v = a then x else y
      apply OMA.two_list_color_from_palette G A L {x, y} left hcross
      · intro v hv
        rw [hAb] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · simpa [left] using hx
        · simpa [left, hab.symm] using hy
      · intro v _
        by_cases h : v = a <;> simp [left, h]
      · intro v hv hsub
        have hvR : v ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩
        have hcard : ({x, y} : Finset ℕ).card ≤ (L v).card := by
          rw [hL v]
          exact Finset.card_le_two
        exact hgood v hvR (Finset.eq_of_subset_of_card_le hsub hcard)

lemma OMA.two_list_small_bipartite (m : ℕ) (hm : m ≤ 5) (G : SimpleGraph (Fin m))
    (hG : G.Colorable 2) : G.IsKChoosable 2 := by
  classical
  obtain ⟨C⟩ := hG
  let A : Finset (Fin m) := Finset.univ.filter fun v => C v = 0
  have hcross {v w} (h : G.Adj v w) : v ∈ A ↔ w ∉ A := by
    have hh : ∀ x y : Fin 2, x ≠ y → (x = 0 ↔ y ≠ 0) := by decide
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hh (C v) (C w) (C.valid h)
  by_cases hA : A.card ≤ 2
  · exact OMA.two_list_small_side m hm G A hA hcross
  · let B := Finset.univ \ A
    have hB : B.card ≤ 2 := by
      dsimp [B]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, Fintype.card_fin]
      omega
    have hcrossB {v w} (h : G.Adj v w) : v ∈ B ↔ w ∉ B := by
      simpa [B] using not_congr (hcross h)
    exact OMA.two_list_small_side m hm G B hB hcrossB

lemma OMA.two_list_six_witness :
    ∃ G : SimpleGraph (Fin 6), G.Colorable 2 ∧ 2 < G.listChromaticNumber := by
  let side (v : Fin 6) : Fin 2 := if v.val < 2 then 0 else 1
  let G : SimpleGraph (Fin 6) :=
    { Adj := fun v w => side v ≠ side w
      symm := ⟨fun _ _ h => Ne.symm h⟩
      loopless := ⟨fun _ h => h rfl⟩ }
  let L : Fin 6 → Finset ℕ := ![{0, 1}, {2, 3}, {0, 2}, {0, 3}, {1, 2}, {1, 3}]
  have hCard (v : Fin 6) : (L v).card = 2 := by fin_cases v <;> decide
  have hnot : ¬ G.IsKChoosable 2 := by
    intro h
    obtain ⟨C, hC⟩ := h L hCard
    have ha : C 0 = 0 ∨ C 0 = 1 := by simpa [L] using hC 0
    have hb : C 1 = 2 ∨ C 1 = 3 := by simpa [L] using hC 1
    have forbid (v : Fin 6) (hv : 2 ≤ v.val) (hL : L v = {C 0, C 1}) : False := by
      have hv0 : G.Adj 0 v := by
        change side 0 ≠ side v
        simp [side, show 1 < v.val by omega]
      have hv1 : G.Adj 1 v := by
        change side 1 ≠ side v
        simp [side, show 1 < v.val by omega]
      have hc := hC v
      rw [hL, Finset.mem_insert, Finset.mem_singleton] at hc
      exact hc.elim (fun he => C.valid hv0 he.symm) (fun he => C.valid hv1 he.symm)
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact forbid 2 (by decide) (by rw [ha, hb]; rfl)
    · exact forbid 3 (by decide) (by rw [ha, hb]; rfl)
    · exact forbid 4 (by decide) (by rw [ha, hb]; rfl)
    · exact forbid 5 (by decide) (by rw [ha, hb]; rfl)
  have hs : {k : ℕ | G.IsKChoosable k}.Nonempty :=
    ⟨Fintype.card (Fin 6), OMA.list_choosable_card G⟩
  have hmin : G.IsKChoosable G.listChromaticNumber := Nat.sInf_mem hs
  refine ⟨G, ⟨Coloring.mk side (fun h => h)⟩, ?_⟩
  by_contra! hle
  exact hnot (OMA.list_choosable_mono hle hmin)

theorem OMA.solution : type_of% @Erdos629.erdos_629.variants.n_two := by
  obtain ⟨G, hBip, hList⟩ := OMA.two_list_six_witness
  have hupper : Erdos629.n 2 ≤ 6 := Erdos629.n_le G hBip hList
  have hExists : {m : ℕ | ∃ H : SimpleGraph (Fin m),
      H.Colorable 2 ∧ 2 < H.listChromaticNumber}.Nonempty := ⟨6, G, hBip, hList⟩
  have hmin : ∃ H : SimpleGraph (Fin (Erdos629.n 2)),
      H.Colorable 2 ∧ 2 < H.listChromaticNumber := Nat.sInf_mem hExists
  apply le_antisymm hupper
  by_contra! hsmall
  obtain ⟨H, hH_bip, hH_list⟩ := hmin
  have hChoosable := OMA.two_list_small_bipartite _ (by omega) H hH_bip
  have hle : H.listChromaticNumber ≤ 2 := Nat.sInf_le hChoosable
  omega