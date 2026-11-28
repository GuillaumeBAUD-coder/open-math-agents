import OMAStatements.S_mo_490846

-- Problem: MathOverflow 490846, conjecture (3) (additive version of the algebraic strengthening
-- of Frankl's union-closed conjecture).
-- Credit: @ShoQo (the argument is the one in the MathOverflow answer to the question)
-- Proof: let U be the union of F; it lies in F. If every subset of U lies in F, any k ∈ U works:
-- A ↦ A ∪ {k} matches the two counts at every weight. Otherwise pick S ⊆ U, S ∉ F, of maximal
-- weight, and k ∈ U \ S. A subset of U heavier than S lies in F, so above the weight of S the map
-- A ↦ A ∪ {k} injects the second family into the first; at the weight of S ∪ {k} it misses
-- S ∪ {k} (as S ∉ F), so the second count is strictly smaller there. Hence the largest weight at
-- which the counts differ has the first count strictly larger.

open OMA.S_mo_490846 Finset

theorem OMA.solution : type_of% @OMA.S_mo_490846.main := by
  classical
  intro n F hF hne y hy
  have hsc : SupClosed (F : Set (Finset (Fin n))) := fun a ha b hb => hF a ha b hb
  obtain ⟨A0, hA0, hA0ne⟩ := hne
  have hFne : F.Nonempty := ⟨A0, hA0⟩
  set U := F.sup id with hUdef
  have hUmem : U ∈ F := hsc.finsetSup_mem hFne (fun i hi => hi)
  have hsub : ∀ A ∈ F, A ⊆ U := fun A hA => Finset.le_sup (f := id) hA
  by_cases hall : ∀ S ⊆ U, S ∈ F
  · obtain ⟨k, hk⟩ := hA0ne
    have hkU : k ∈ U := hsub A0 hA0 hk
    refine ⟨k, Or.inl fun s => ?_⟩
    unfold L R
    symm
    apply Finset.card_bij' (fun A _ => insert k A) (fun B _ => B.erase k)
    · intro A hA
      simp only [mem_filter] at hA
      exact erase_insert hA.2.1
    · intro B hB
      simp only [mem_filter] at hB
      exact insert_erase hB.2.1
    · intro A hA
      simp only [mem_filter] at hA ⊢
      exact ⟨hall _ (insert_subset hkU (hsub A hA.1)), mem_insert_self _ _, hA.2.2⟩
    · intro B hB
      simp only [mem_filter] at hB ⊢
      refine ⟨hall _ ((erase_subset _ _).trans (hsub B hB.1)), notMem_erase _ _, ?_⟩
      rw [insert_erase hB.2.1]; exact hB.2.2
  · push Not at hall
    obtain ⟨S, hSU, hSF, hSmax⟩ : ∃ S ⊆ U, S ∉ F ∧
        ∀ B ⊆ U, B ∉ F → ∑ i ∈ B, y i ≤ ∑ i ∈ S, y i := by
      have hC : (U.powerset.filter (fun S => S ∉ F)).Nonempty := by
        obtain ⟨S, hS, hSF⟩ := hall
        exact ⟨S, by simp [hS, hSF]⟩
      obtain ⟨S, hSC, hSmax⟩ := (U.powerset.filter (fun S => S ∉ F)).exists_max_image
        (fun S => ∑ i ∈ S, y i) hC
      simp only [mem_filter, mem_powerset] at hSC
      exact ⟨S, hSC.1, hSC.2, fun B hB hBF => hSmax B (by simp [hB, hBF])⟩
    have hbig : ∀ B ⊆ U, ∑ i ∈ S, y i < ∑ i ∈ B, y i → B ∈ F := by
      intro B hB hlt
      by_contra hBF
      have := hSmax B hB hBF
      linarith
    have hSneU : S ≠ U := fun h => hSF (h ▸ hUmem)
    obtain ⟨k, hkU, hkS⟩ : ∃ k ∈ U, k ∉ S := by
      by_contra hcon
      push Not at hcon
      exact hSneU (Finset.Subset.antisymm hSU hcon)
    refine ⟨k, Or.inr ?_⟩
    -- above the weight of S, adding k injects the second family into the first
    have hle : ∀ t, ∑ i ∈ S, y i < t → R F y k t ≤ L F y k t := by
      intro t ht
      unfold L R
      apply Finset.card_le_card_of_injOn (fun A => insert k A)
      · intro A hA
        simp only [coe_filter, Set.mem_ofPred_eq, mem_filter] at hA ⊢
        refine ⟨hbig _ (insert_subset hkU (hsub A hA.1)) ?_, mem_insert_self _ _, hA.2.2⟩
        rw [hA.2.2]; exact ht
      · intro A hA B hB hAB
        simp only [coe_filter, Set.mem_ofPred_eq] at hA hB
        have := congrArg (fun X => X.erase k) hAB
        simpa [erase_insert hA.2.1, erase_insert hB.2.1] using this
    set t0 := ∑ i ∈ insert k S, y i with ht0def
    have ht0 : ∑ i ∈ S, y i < t0 := by
      rw [ht0def, sum_insert hkS]; linarith [hy k]
    have hSkF : insert k S ∈ F := hbig _ (insert_subset hkU hSU) ht0
    have hlt : R F y k t0 < L F y k t0 := by
      unfold L R
      set Rs := F.filter fun A => k ∉ A ∧ ∑ i ∈ insert k A, y i = t0
      set Ls := F.filter fun A => k ∈ A ∧ ∑ i ∈ A, y i = t0
      have hxL : insert k S ∈ Ls := by
        simp only [Ls, mem_filter]; exact ⟨hSkF, mem_insert_self _ _, rfl⟩
      have hinj : Set.InjOn (fun A => insert k A) (Rs : Set (Finset (Fin n))) := by
        intro A hA B hB hAB
        simp only [Rs, coe_filter, Set.mem_ofPred_eq] at hA hB
        have := congrArg (fun X => X.erase k) hAB
        simpa [erase_insert hA.2.1, erase_insert hB.2.1] using this
      have himg : Rs.image (fun A => insert k A) ⊆ Ls.erase (insert k S) := by
        intro B hB
        obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
        simp only [Rs, mem_filter] at hA
        refine mem_erase.2 ⟨?_, ?_⟩
        · intro hAS
          have := congrArg (fun X => X.erase k) hAS
          simp only [erase_insert hA.2.1, erase_insert hkS] at this
          exact hSF (this ▸ hA.1)
        · simp only [Ls, mem_filter]
          refine ⟨hbig _ (insert_subset hkU (hsub A hA.1)) ?_, mem_insert_self _ _, hA.2.2⟩
          rw [hA.2.2]; exact ht0
      calc Rs.card = (Rs.image (fun A => insert k A)).card := (card_image_of_injOn hinj).symm
        _ ≤ (Ls.erase (insert k S)).card := card_le_card himg
        _ < Ls.card := card_erase_lt_of_mem hxL
    -- the counts can only differ at weights of members of F
    set T := (F.image fun A => ∑ i ∈ A, y i) ∪ (F.image fun A => ∑ i ∈ insert k A, y i)
    have hT : ∀ t, L F y k t ≠ R F y k t → t ∈ T := by
      intro t h
      by_contra hT
      have h1 : L F y k t = 0 := by
        unfold L
        rw [card_eq_zero, filter_eq_empty_iff]
        rintro A hA ⟨-, hAt⟩
        exact hT (mem_union_left _ (mem_image.2 ⟨A, hA, hAt⟩))
      have h2 : R F y k t = 0 := by
        unfold R
        rw [card_eq_zero, filter_eq_empty_iff]
        rintro A hA ⟨-, hAt⟩
        exact hT (mem_union_right _ (mem_image.2 ⟨A, hA, hAt⟩))
      exact h (h1.trans h2.symm)
    set D := T.filter fun t => L F y k t ≠ R F y k t
    have ht0D : t0 ∈ D := mem_filter.2 ⟨hT _ hlt.ne', hlt.ne'⟩
    have hsD : D.max' ⟨t0, ht0D⟩ ∈ D := D.max'_mem _
    have hs0 : t0 ≤ D.max' ⟨t0, ht0D⟩ := D.le_max' _ ht0D
    refine ⟨D.max' ⟨t0, ht0D⟩, ?_, ?_⟩
    · have hne' := (mem_filter.1 hsD).2
      exact lt_of_le_of_ne (hle _ (by linarith)) (Ne.symm hne')
    · intro t hst
      by_contra hne'
      have := D.le_max' t (mem_filter.2 ⟨hT t hne', hne'⟩)
      linarith
