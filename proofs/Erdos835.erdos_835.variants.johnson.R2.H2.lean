import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R2

open Finset

private theorem singleton_extension {α : Type*} [DecidableEq α] {T A : Finset α}
    (hSub : T ⊆ A) (hCard : T.card+1 = A.card) :
    ∃ x ∉ T, A = insert x T := by
  have hDiff : (A \ T).card = 1 := by rw [card_sdiff_of_subset hSub]; omega
  obtain ⟨x,hx⟩ := card_eq_one.mp hDiff
  have hx' : x ∈ A \ T := by simp [hx]
  obtain ⟨hxa,hxt⟩ := mem_sdiff.mp hx'
  refine ⟨x,hxt,(eq_of_subset_of_card_le (insert_subset hxa hSub) ?_).symm⟩
  rw [card_insert_of_notMem hxt,hCard]

theorem OMA.solution : OMA.R_Erdos835_erdos_835_variants_johnson_R2.H2 := by
  classical
  intro p _ hp c hC A B hA hB hi hEq
  let T := A ∩ B
  have hT : T.card = p-3 := hi
  obtain ⟨x,hx,hAx⟩ := singleton_extension (T := T) (A := A) inter_subset_left (by omega)
  obtain ⟨y,hy,hBy⟩ := singleton_extension (T := T) (A := B) inter_subset_right (by omega)
  let f : (Tᶜ : Finset (Fin (2*p-3))) → Fin p := fun z => c (insert z.val T)
  have hSurj : Function.Surjective f := by
    intro k
    obtain ⟨z,hz,hc⟩ := hC T hT k
    exact ⟨⟨z,mem_compl.mpr hz⟩,hc⟩
  have hSize : Fintype.card (↥(Tᶜ : Finset (Fin (2*p-3)))) = Fintype.card (Fin p) := by
    rw [Fintype.card_coe,card_compl,Fintype.card_fin,Fintype.card_fin,hT]
    omega
  have hInj := ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hSurj,hSize⟩).1
  have hxy : x = y := congrArg Subtype.val
    (hInj (a₁ := ⟨x,mem_compl.mpr hx⟩) (a₂ := ⟨y,mem_compl.mpr hy⟩) (by
      simpa only [f,← hAx,← hBy] using hEq))
  have hab : A = B := hAx.trans (hxy ▸ hBy).symm
  rw [hab, inter_self, hB] at hi
  omega
