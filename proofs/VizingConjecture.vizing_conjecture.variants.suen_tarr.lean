import FormalConjectures.Wikipedia.VizingConjecture

-- Problem: The Suen–Tarr inequality (2012).
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/VizingConjecture.lean:81 (declaration VizingConjecture.vizing_conjecture.variants.suen_tarr)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open SimpleGraph Finset

-- Suen–Tarr (2012): Clark–Suen double counting, run once from a γ-set of G and, when some
-- cell is tight, once more from the resulting γ-set of H.
theorem OMA.solution : type_of% @VizingConjecture.vizing_conjecture.variants.suen_tarr := by
  intro α β _ _ _ _ G H
  classical
  have coreA : ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (G : SimpleGraph α) (H : SimpleGraph β) (D : Finset (α × β)),
      (G □ H).IsDominating (D : Set (α × β)) → ∀ (U : Finset α),
      G.IsDominating (U : Set α) → U.card ≤ G.dominationNumber →
      ∃ P C : α → Finset β,
        (∀ x ∈ U, H.IsDominating ((P x ∪ C x : Finset β) : Set β)) ∧
        (∀ x ∈ U, ∀ v ∈ P x ∪ C x, ∃ u, (u, v) ∈ D) ∧
        ∑ x ∈ U, (P x).card ≤ D.card ∧
        ∑ x ∈ U, (C x).card + (D.filter (fun p => p.1 ∈ U)).card ≤ D.card := by
    intro α β _ _ _ _ G H D hD U hU hUc
    classical
    have hπ : ∀ u, ∃ x ∈ U, (u ∈ U → x = u) ∧ (x = u ∨ G.Adj u x) := by
      intro u
      by_cases hu : u ∈ U
      · exact ⟨u, hu, fun _ => rfl, Or.inl rfl⟩
      · rcases hU u with h | ⟨w, hw, hadj⟩
        · exact absurd (Finset.mem_coe.1 h) hu
        · exact ⟨w, Finset.mem_coe.1 hw, fun h => absurd h hu, Or.inr hadj⟩
    choose π hπU hπfix hπadj using hπ
    let P : α → Finset β := fun x => (D.filter (fun p => π p.1 = x)).image Prod.snd
    let C : α → Finset β := fun x => univ.filter (fun v => v ∉ P x ∧ ∀ w ∈ P x, ¬ H.Adj v w)
    have memP : ∀ x v, v ∈ P x ↔ ∃ u, π u = x ∧ (u, v) ∈ D := by
      intro x v
      simp only [P, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨⟨u, v'⟩, ⟨hD', hπ'⟩, rfl⟩
        exact ⟨u, hπ', hD'⟩
      · rintro ⟨u, hu, huv⟩
        exact ⟨(u, v), ⟨huv, hu⟩, rfl⟩
    have memC : ∀ x v, v ∈ C x ↔ v ∉ P x ∧ ∀ w ∈ P x, ¬ H.Adj v w := by
      intro x v
      simp [C]
    refine ⟨P, C, ?_, ?_, ?_, ?_⟩
    · intro x _ v
      by_cases h1 : v ∈ P x
      · exact Or.inl (by simp [h1])
      · by_cases h2 : ∃ w ∈ P x, H.Adj v w
        · obtain ⟨w, hw, hadj⟩ := h2
          exact Or.inr ⟨w, by simp [hw], hadj⟩
        · push Not at h2
          exact Or.inl (by simp [(memC x v).2 ⟨h1, h2⟩])
    · intro x hx v hv
      rcases Finset.mem_union.1 hv with h | h
      · obtain ⟨u, -, huv⟩ := (memP x v).1 h
        exact ⟨u, huv⟩
      · rcases hD (x, v) with h' | ⟨⟨u', v'⟩, hq, hadj⟩
        · exact ⟨x, Finset.mem_coe.1 h'⟩
        · rw [boxProd_adj] at hadj
          rcases hadj with ⟨-, h2⟩ | ⟨h1, h2⟩
          · simp only at h2
            subst h2
            exact ⟨u', Finset.mem_coe.1 hq⟩
          · simp only at h1 h2
            subst h2
            have : v' ∈ P x := (memP x v').2 ⟨x, hπfix x hx, Finset.mem_coe.1 hq⟩
            exact absurd h1 (((memC x v).1 h).2 v' this)
    · have hmaps : (D : Set (α × β)).MapsTo (fun p => π p.1) U := fun p _ => hπU p.1
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      exact Finset.sum_le_sum fun x _ => Finset.card_image_le
    · -- per-v bound
      have hv : ∀ v : β, (U.filter (fun x => v ∈ C x)).card +
          (U.filter (fun x => (x, v) ∈ D)).card ≤ (univ.filter (fun u => (u, v) ∈ D)).card := by
        intro v
        set S := U.filter (fun x => v ∈ C x)
        set Dv := univ.filter (fun u => (u, v) ∈ D)
        set Uh := U.filter (fun x => (x, v) ∈ D)
        have hX : G.IsDominating ((Dv ∪ (U \ S) : Finset α) : Set α) := by
          intro u
          by_cases hS : π u ∈ S
          · have hvC : v ∈ C (π u) := (Finset.mem_filter.1 hS).2
            rcases hD (u, v) with h' | ⟨⟨u', v'⟩, hq, hadj⟩
            · exact Or.inl (by simp [Dv, Finset.mem_coe.1 h'])
            · rw [boxProd_adj] at hadj
              rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · simp only at h1 h2
                subst h2
                exact Or.inr ⟨u', by simp [Dv, Finset.mem_coe.1 hq], h1⟩
              · simp only at h1 h2
                subst h2
                have : v' ∈ P (π u) := (memP _ v').2 ⟨u, rfl, Finset.mem_coe.1 hq⟩
                exact absurd h1 (((memC _ v).1 hvC).2 v' this)
          · have hmem : π u ∈ Dv ∪ (U \ S) := by simp [hπU u, hS]
            rcases hπadj u with h | h
            · exact Or.inl (by rw [← h]; exact Finset.mem_coe.2 hmem)
            · exact Or.inr ⟨π u, Finset.mem_coe.2 hmem, h⟩
        have h1 := dominationNumber_le_of_isDominating G _ hX
        have h2 := Finset.card_union_add_card_inter Dv (U \ S)
        have hsub : Uh ⊆ Dv ∩ (U \ S) := by
          intro x hx
          obtain ⟨hxU, hxD⟩ := Finset.mem_filter.1 hx
          have hvP : v ∈ P x := (memP x v).2 ⟨x, hπfix x hxU, hxD⟩
          have : x ∉ S := by
            intro hxS
            exact ((memC x v).1 (Finset.mem_filter.1 hxS).2).1 hvP
          simp [Dv, hxD, hxU, this]
        have h3 := Finset.card_le_card hsub
        have h4 : (U \ S).card = U.card - S.card := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.2 (Finset.filter_subset _ _)]
        have h5 : S.card ≤ U.card := Finset.card_le_card (Finset.filter_subset _ _)
        omega
      have e1 : ∑ x ∈ U, (C x).card = ∑ v : β, (U.filter (fun x => v ∈ C x)).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [C]
      have e2 : D.card = ∑ v : β, (univ.filter (fun u => (u, v) ∈ D)).card := by
        have hmaps : (D : Set (α × β)).MapsTo Prod.snd (univ : Finset β) := fun _ _ => mem_univ _
        rw [Finset.card_eq_sum_card_fiberwise hmaps]
        refine Finset.sum_congr rfl fun v _ => ?_
        apply Finset.card_bij (fun p _ => p.1)
        · intro p hp
          obtain ⟨hpD, rfl⟩ := Finset.mem_filter.1 hp
          simp [hpD]
        · intro p hp q hq hpq
          obtain ⟨-, hp2⟩ := Finset.mem_filter.1 hp
          obtain ⟨-, hq2⟩ := Finset.mem_filter.1 hq
          exact Prod.ext hpq (hp2.trans hq2.symm)
        · intro u hu
          exact ⟨(u, v), by simpa using hu, rfl⟩
      have e3 : (D.filter (fun p => p.1 ∈ U)).card = ∑ v : β, (U.filter (fun x => (x, v) ∈ D)).card := by
        have hmaps : ((D.filter (fun p => p.1 ∈ U)) : Set (α × β)).MapsTo Prod.snd (univ : Finset β) :=
          fun _ _ => mem_univ _
        rw [Finset.card_eq_sum_card_fiberwise hmaps]
        refine Finset.sum_congr rfl fun v _ => ?_
        apply Finset.card_bij (fun p _ => p.1)
        · intro p hp
          simp only [Finset.mem_filter] at hp
          obtain ⟨⟨hpD, hpU⟩, rfl⟩ := hp
          simp [hpD, hpU]
        · intro p hp q hq hpq
          simp only [Finset.mem_filter] at hp hq
          exact Prod.ext hpq (hp.2.trans hq.2.symm)
        · intro u hu
          simp only [Finset.mem_filter] at hu
          exact ⟨(u, v), by simp [hu.1, hu.2], rfl⟩
      rw [e1, e2, e3, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun v _ => hv v
  obtain ⟨D, hD, hDc⟩ := exists_isNDominatingSet_dominationNumber (G □ H)
  obtain ⟨U, hU, hUc⟩ := exists_isNDominatingSet_dominationNumber G
  obtain ⟨P, C, hdom, hex, hP, hC⟩ := coreA G H D hD U hU hUc.le
  have hge : ∀ x ∈ U, H.dominationNumber ≤ (P x).card + (C x).card := fun x hx =>
    (dominationNumber_le_of_isDominating H _ (hdom x hx)).trans (card_union_le _ _)
  by_cases hcase : ∀ x ∈ U, H.dominationNumber + 1 ≤ (P x).card + (C x).card
  · have hs := Finset.sum_le_sum hcase
    rw [sum_const, smul_eq_mul, sum_add_distrib, hUc, Nat.mul_succ] at hs
    have := min_le_left G.dominationNumber H.dominationNumber
    have hcomm : G.dominationNumber * H.dominationNumber =
      G.dominationNumber * H.dominationNumber := rfl
    omega
  · push Not at hcase
    obtain ⟨x0, hx0, hlt⟩ := hcase
    set W := P x0 ∪ C x0 with hWdef
    have hW : H.dominationNumber ≤ W.card := dominationNumber_le_of_isDominating _ _ (hdom x0 hx0)
    have hWle : W.card ≤ H.dominationNumber := (card_union_le _ _).trans (by omega)
    set D' := D.image Prod.swap with hD'def
    have hD'c : D'.card = D.card := card_image_of_injective _ Prod.swap_injective
    have hD' : (H □ G).IsDominating (D' : Set (β × α)) := by
      rintro ⟨v, u⟩
      rcases hD (u, v) with h | ⟨⟨u', v'⟩, hq, hadj⟩
      · exact Or.inl (by simp [D', Finset.mem_coe.1 h])
      · refine Or.inr ⟨(v', u'), by simp [D', Finset.mem_coe.1 hq], ?_⟩
        rw [boxProd_adj] at hadj ⊢
        simp only at hadj ⊢
        tauto
    obtain ⟨P', C', hdom', -, hP', hC'⟩ := coreA H G D' hD' W (hdom x0 hx0) hWle
    have hcount : W.card ≤ (D'.filter (fun p => p.1 ∈ W)).card := by
      apply Finset.card_le_card_of_surjOn Prod.fst
      intro w hw
      obtain ⟨u, hu⟩ := hex x0 hx0 w (Finset.mem_coe.1 hw)
      exact ⟨(w, u), by simp [D', hu, Finset.mem_coe.1 hw], rfl⟩
    have hge' : ∀ w ∈ W, G.dominationNumber ≤ (P' w).card + (C' w).card := fun w hw =>
      (dominationNumber_le_of_isDominating G _ (hdom' w hw)).trans (card_union_le _ _)
    have hs := Finset.sum_le_sum hge'
    rw [sum_const, smul_eq_mul, sum_add_distrib] at hs
    have hWeq : W.card = H.dominationNumber := le_antisymm hWle hW
    rw [hWeq] at hs hcount
    have := min_le_right G.dominationNumber H.dominationNumber
    rw [Nat.mul_comm] at hs
    omega
