import OMAReductions.R_Erdos643_erdos_643_parts_ii_R1_H1_R1

open scoped Classical in
theorem OMA.solution : OMA.R_Erdos643_erdos_643_parts_ii_R1_H1_R1.H2 := by
  intro n H huniform hhall
  let E := {e : Finset (Fin n) // e ∈ H}
  let P : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard 2
  let r : E → Finset (Fin n) → Prop := fun x p ↦ p ∈ x.1.powersetCard 2
  have hh : ∀ A : Finset E, A.card ≤ (Finset.univ.filter fun p ↦ ∃ a ∈ A, r a p).card := by
    intro A
    let F : Finset (Finset (Fin n)) := A.image Subtype.val
    have hFsub : F ⊆ H := by
      intro e he
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
      exact x.2
    have hFcard : F.card = A.card := by
      dsimp [F]
      exact Finset.card_image_of_injective A Subtype.val_injective
    have hshadow :
        (((Finset.univ : Finset (Fin n)).powersetCard 2).filter
          fun p ↦ ∃ e ∈ F, p ⊆ e) =
          Finset.univ.filter fun p ↦ ∃ a ∈ A, r a p := by
      ext p
      constructor
      · intro hp
        rw [Finset.mem_filter] at hp ⊢
        obtain ⟨hpair, e, heF, hpe⟩ := hp
        obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.mp heF
        exact ⟨Finset.mem_univ _, ⟨x, hxA,
          Finset.mem_powersetCard.mpr ⟨hpe, (Finset.mem_powersetCard.mp hpair).2⟩⟩⟩
      · intro hp
        rw [Finset.mem_filter] at hp ⊢
        obtain ⟨_, x, hxA, hxp⟩ := hp
        obtain ⟨hpx, hp2⟩ := Finset.mem_powersetCard.mp hxp
        exact ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hp2⟩,
          ⟨x.1, Finset.mem_image.mpr ⟨x, hxA, rfl⟩, hpx⟩⟩
    calc
      A.card = F.card := hFcard.symm
      _ ≤ (((Finset.univ : Finset (Fin n)).powersetCard 2).filter
          fun p ↦ ∃ e ∈ F, p ⊆ e).card := hhall F hFsub
      _ = (Finset.univ.filter fun p ↦ ∃ a ∈ A, r a p).card := by rw [hshadow]
  obtain ⟨f, hfinj, hfr⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective r).mp hh
  have hfP : ∀ x : E, f x ∈ P := by
    intro x
    have hx := hfr x
    obtain ⟨_, hp2⟩ := Finset.mem_powersetCard.mp hx
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hp2⟩
  let Q := {p : Finset (Fin n) // p ∈ P}
  let g : E → Q := fun x ↦ ⟨f x, hfP x⟩
  have hg : Function.Injective g := by
    intro x y hxy
    apply hfinj
    exact congrArg Subtype.val hxy
  calc
    H.card = Fintype.card E := by
      simpa [E] using (Fintype.card_coe H).symm
    _ ≤ Fintype.card Q := Fintype.card_le_of_injective g hg
    _ = P.card := Fintype.card_coe P
    _ = n.choose 2 := by
      simp [P, Finset.card_powersetCard]
