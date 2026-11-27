import OMAReductions.R_Erdos724_erdos_724_variants_wilson_R1

open Finset

namespace OMAMacNeish

/-- A family of `s` mutually orthogonal Latin squares on the type `α`. -/
def Fam (α : Type) (s : ℕ) : Prop :=
  ∃ f : Fin s → α → α → α,
    (∀ i x, Function.Injective (f i x)) ∧
    (∀ i y, Function.Injective (fun x => f i x y)) ∧
    (∀ i j, i ≠ j → Function.Injective (fun p : α × α => (f i p.1 p.2, f j p.1 p.2)))

lemma fam_prod {α β : Type} {s : ℕ} (hα : Fam α s) (hβ : Fam β s) : Fam (α × β) s := by
  obtain ⟨f, hf1, hf2, hf3⟩ := hα
  obtain ⟨g, hg1, hg2, hg3⟩ := hβ
  refine ⟨fun i p q => (f i p.1 q.1, g i p.2 q.2), ?_, ?_, ?_⟩
  · intro i x y z h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (hf1 i x.1 h.1) (hg1 i x.2 h.2)
  · intro i y x z h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (hf2 i y.1 h.1) (hg2 i y.2 h.2)
  · intro i j hij p q h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    have ha := hf3 i j hij (a₁ := (p.1.1, p.2.1)) (a₂ := (q.1.1, q.2.1))
      (by simp only [Prod.mk.injEq]; exact ⟨h1, h3⟩)
    have hb := hg3 i j hij (a₁ := (p.1.2, p.2.2)) (a₂ := (q.1.2, q.2.2))
      (by simp only [Prod.mk.injEq]; exact ⟨h2, h4⟩)
    simp only [Prod.mk.injEq] at ha hb
    exact Prod.ext (Prod.ext ha.1 hb.1) (Prod.ext ha.2 hb.2)

lemma fam_equiv {α β : Type} {s : ℕ} (e : α ≃ β) (h : Fam α s) : Fam β s := by
  obtain ⟨f, hf1, hf2, hf3⟩ := h
  refine ⟨fun i x y => e (f i (e.symm x) (e.symm y)), ?_, ?_, ?_⟩
  · intro i x y z h
    exact e.symm.injective (hf1 i _ (e.injective h))
  · intro i y x z h
    exact e.symm.injective (hf2 i _ (e.injective h))
  · intro i j hij p q h
    simp only [Prod.mk.injEq] at h
    have h' := hf3 i j hij (a₁ := (e.symm p.1, e.symm p.2)) (a₂ := (e.symm q.1, e.symm q.2))
      (by simp only [Prod.mk.injEq]; exact ⟨e.injective h.1, e.injective h.2⟩)
    simp only [Prod.mk.injEq] at h'
    exact Prod.ext (e.symm.injective h'.1) (e.symm.injective h'.2)

lemma bdd (n : ℕ) : BddAbove {k : ℕ | ∃ S : Finset (LatinSquare n), #S = k ∧
    (S : Set (LatinSquare n)).Pairwise Erdos724.IsOrthogonal} := by
  refine ⟨Fintype.card (LatinSquare n), ?_⟩
  rintro k ⟨S, rfl, -⟩
  exact card_le_univ S

lemma fam_of_le (n s : ℕ) (hs : s ≤ Erdos724.maxMOLS n) : Fam (Fin n) s := by
  have hmem : Erdos724.maxMOLS n ∈ {k : ℕ | ∃ S : Finset (LatinSquare n), #S = k ∧
      (S : Set (LatinSquare n)).Pairwise Erdos724.IsOrthogonal} :=
    Nat.sSup_mem ⟨0, ∅, by simp, by simp⟩ (bdd n)
  obtain ⟨S, hcard, hpair⟩ := hmem
  obtain ⟨S', hS', hcard'⟩ := Finset.exists_subset_card_eq (hcard ▸ hs)
  let e : Fin s ≃ S' := (Finset.equivFinOfCardEq hcard').symm
  refine ⟨fun i => (e i).1.mat, ?_, ?_, ?_⟩
  · intro i x
    exact (e i).1.row_injective x
  · intro i y
    exact (e i).1.col_injective y
  · intro i j hij
    have hne : (e i).1 ≠ (e j).1 := fun h => hij (e.injective (Subtype.ext h))
    exact hpair (hS' (e i).2) (hS' (e j).2) hne

lemma le_of_fam (n s : ℕ) (hn : 2 ≤ n) (h : Fam (Fin n) s) : s ≤ Erdos724.maxMOLS n := by
  classical
  obtain ⟨f, hf1, hf2, hf3⟩ := h
  let L : Fin s → LatinSquare n := fun i =>
    { mat := f i, row_injective := hf1 i, col_injective := hf2 i }
  have hinj : Function.Injective L := by
    intro i j hij
    by_contra hne
    have h3 := hf3 i j hne
    have hmat : f i = f j := congrArg LatinSquare.mat hij
    have h0 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
      intro h
      simp only [Fin.mk.injEq] at h
      omega
    obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 (hf1 i ⟨1, by omega⟩))
      (f i ⟨0, by omega⟩ ⟨0, by omega⟩)
    have := h3 (a₁ := (⟨0, by omega⟩, ⟨0, by omega⟩)) (a₂ := (⟨1, by omega⟩, y))
      (by simp only [Prod.mk.injEq]; rw [← hmat]; exact ⟨hy.symm, hy.symm⟩)
    simp only [Prod.mk.injEq] at this
    exact h0 this.1
  refine le_csSup (bdd n) ⟨Finset.univ.image L, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro A hA B hB hAB
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hA hB
    obtain ⟨i, rfl⟩ := hA
    obtain ⟨j, rfl⟩ := hB
    exact hf3 i j (fun h => hAB (congrArg L h))

end OMAMacNeish

theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_wilson_R1.H2 := by
  intro a b ha hb
  rcases Nat.lt_or_ge (a * b) 2 with hab | hab
  · have ha1 : a = 1 := by nlinarith
    have hb1 : b = 1 := by nlinarith
    subst ha1
    subst hb1
    simp
  · obtain ⟨s, hs⟩ : ∃ s, s = min (Erdos724.maxMOLS a) (Erdos724.maxMOLS b) := ⟨_, rfl⟩
    rw [← hs]
    have h1 := OMAMacNeish.fam_of_le a s (hs ▸ min_le_left _ _)
    have h2 := OMAMacNeish.fam_of_le b s (hs ▸ min_le_right _ _)
    exact OMAMacNeish.le_of_fam (a * b) s hab
      (OMAMacNeish.fam_equiv finProdFinEquiv (OMAMacNeish.fam_prod h1 h2))
