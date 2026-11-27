import OMAReductions.R_Erdos724_erdos_724_variants_wilson_R1

-- Step Erdos724.erdos_724.variants.wilson.R1.H2: hypothesis H2 of reduction Erdos724.erdos_724.variants.wilson.R1

/-!
MacNeish's product bound. Identify `Fin (a * b)` with `Fin a × Fin b` and form the product square
`(L ⊗ M) x y = (L x₁ y₁, M x₂ y₂)`. If `L ⟂ L'` and `M ⟂ M'` then `L ⊗ M ⟂ L' ⊗ M'`, and `L ⊗ M`
determines `L` when `b ≥ 1`. Take `s = min (N a) (N b)` pairwise orthogonal squares of each order,
match them by a bijection and form the `s` products: they are distinct and pairwise orthogonal.
-/

open Erdos724
open scoped Classical

namespace OMA

/-- The identification of `Fin a × Fin b` with `Fin (a * b)`. -/
def E (a b : ℕ) : Fin a × Fin b ≃ Fin (a * b) := finProdFinEquiv

/-- The product of two Latin squares. -/
def prodLS {a b : ℕ} (L : LatinSquare a) (M : LatinSquare b) : LatinSquare (a * b) where
  mat := fun x y => E a b (L.mat ((E a b).symm x).1 ((E a b).symm y).1,
    M.mat ((E a b).symm x).2 ((E a b).symm y).2)
  row_injective := by
    intro x y y' h
    have h0 : E a b (L.mat ((E a b).symm x).1 ((E a b).symm y).1,
          M.mat ((E a b).symm x).2 ((E a b).symm y).2) =
        E a b (L.mat ((E a b).symm x).1 ((E a b).symm y').1,
          M.mat ((E a b).symm x).2 ((E a b).symm y').2) := h
    have h' := Prod.mk.inj ((E a b).injective h0)
    exact (E a b).symm.injective
      (Prod.ext (L.row_injective _ h'.1) (M.row_injective _ h'.2))
  col_injective := by
    intro y x x' h
    have h0 : E a b (L.mat ((E a b).symm x).1 ((E a b).symm y).1,
          M.mat ((E a b).symm x).2 ((E a b).symm y).2) =
        E a b (L.mat ((E a b).symm x').1 ((E a b).symm y).1,
          M.mat ((E a b).symm x').2 ((E a b).symm y).2) := h
    have h' := Prod.mk.inj ((E a b).injective h0)
    exact (E a b).symm.injective
      (Prod.ext (L.col_injective _ h'.1) (M.col_injective _ h'.2))

theorem prodLS_mat {a b : ℕ} (L : LatinSquare a) (M : LatinSquare b) (x y : Fin (a * b)) :
    (prodLS L M).mat x y = E a b (L.mat ((E a b).symm x).1 ((E a b).symm y).1,
      M.mat ((E a b).symm x).2 ((E a b).symm y).2) := rfl

theorem prod_orth {a b : ℕ} (L L' : LatinSquare a) (M M' : LatinSquare b)
    (h1 : IsOrthogonal L L') (h2 : IsOrthogonal M M') :
    IsOrthogonal (prodLS L M) (prodLS L' M') := by
  unfold IsOrthogonal at h1 h2 ⊢
  intro p q h
  obtain ⟨x, y⟩ := p
  obtain ⟨x', y'⟩ := q
  have hA : (prodLS L M).mat x y = (prodLS L M).mat x' y' := congrArg Prod.fst h
  have hB : (prodLS L' M').mat x y = (prodLS L' M').mat x' y' := congrArg Prod.snd h
  rw [prodLS_mat, prodLS_mat] at hA hB
  have hA' := Prod.mk.inj ((E a b).injective hA)
  have hB' := Prod.mk.inj ((E a b).injective hB)
  have hp := Prod.mk.inj (@h1 (((E a b).symm x).1, ((E a b).symm y).1)
    (((E a b).symm x').1, ((E a b).symm y').1) (Prod.ext hA'.1 hB'.1))
  have hq := Prod.mk.inj (@h2 (((E a b).symm x).2, ((E a b).symm y).2)
    (((E a b).symm x').2, ((E a b).symm y').2) (Prod.ext hA'.2 hB'.2))
  have hx : x = x' := (E a b).symm.injective (Prod.ext hp.1 hq.1)
  have hy : y = y' := (E a b).symm.injective (Prod.ext hp.2 hq.2)
  rw [hx, hy]

theorem prod_left_inj {a b : ℕ} (hb : 0 < b) (L L' : LatinSquare a) (M M' : LatinSquare b)
    (h : prodLS L M = prodLS L' M') : L = L' := by
  have hmat : L.mat = L'.mat := by
    funext i j
    have h1 : (prodLS L M).mat (E a b (i, ⟨0, hb⟩)) (E a b (j, ⟨0, hb⟩)) =
        (prodLS L' M').mat (E a b (i, ⟨0, hb⟩)) (E a b (j, ⟨0, hb⟩)) := by rw [h]
    rw [prodLS_mat, prodLS_mat] at h1
    have h2 := (Prod.mk.inj ((E a b).injective h1)).1
    simp only [Equiv.symm_apply_apply] at h2
    exact h2
  cases L
  cases L'
  simp only [LatinSquare.mk.injEq]
  exact hmat

end OMA

theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_wilson_R1.H2 := by
  unfold OMA.R_Erdos724_erdos_724_variants_wilson_R1.H2
  intro a b _ hb
  have hatt : ∀ n : ℕ, ∃ S : Finset (LatinSquare n), S.card = maxMOLS n ∧
      (S : Set (LatinSquare n)).Pairwise IsOrthogonal := by
    intro n
    have hne : {k : ℕ | ∃ S : Finset (LatinSquare n), S.card = k ∧
        (S : Set (LatinSquare n)).Pairwise IsOrthogonal}.Nonempty := ⟨0, ∅, rfl, by simp⟩
    have hbdd : BddAbove {k : ℕ | ∃ S : Finset (LatinSquare n), S.card = k ∧
        (S : Set (LatinSquare n)).Pairwise IsOrthogonal} :=
      ⟨Fintype.card (LatinSquare n), by
        rintro k ⟨S, rfl, -⟩
        exact Finset.card_le_univ S⟩
    exact Nat.sSup_mem hne hbdd
  obtain ⟨Sa, hSa, hPa⟩ := hatt a
  obtain ⟨Sb, hSb, hPb⟩ := hatt b
  obtain ⟨A', hAsub, hAcard⟩ := Finset.exists_subset_card_eq
    (show min (maxMOLS a) (maxMOLS b) ≤ Sa.card by rw [hSa]; exact min_le_left _ _)
  obtain ⟨B', hBsub, hBcard⟩ := Finset.exists_subset_card_eq
    (show min (maxMOLS a) (maxMOLS b) ≤ Sb.card by rw [hSb]; exact min_le_right _ _)
  obtain ⟨φ⟩ : Nonempty (A' ≃ B') := ⟨Finset.equivOfCardEq (hAcard.trans hBcard.symm)⟩
  have hinj : Function.Injective (fun L : A' => OMA.prodLS L.1 (φ L).1) := by
    intro L L' h
    exact Subtype.ext (OMA.prod_left_inj hb _ _ _ _ h)
  show min (maxMOLS a) (maxMOLS b) ≤ sSup {k : ℕ | ∃ S : Finset (LatinSquare (a * b)),
    S.card = k ∧ (S : Set (LatinSquare (a * b))).Pairwise IsOrthogonal}
  refine le_csSup ⟨Fintype.card (LatinSquare (a * b)), ?_⟩
    ⟨A'.attach.image (fun L => OMA.prodLS L.1 (φ L).1), ?_, ?_⟩
  · rintro k ⟨S, rfl, -⟩
    exact Finset.card_le_univ S
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_attach, hAcard]
  · intro X hX Y hY hXY
    obtain ⟨L, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hX)
    obtain ⟨L', _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hY)
    have hne : L ≠ L' := fun h => hXY (by rw [h])
    apply OMA.prod_orth
    · exact hPa (Finset.mem_coe.mpr (hAsub L.2)) (Finset.mem_coe.mpr (hAsub L'.2))
        (fun h => hne (Subtype.ext h))
    · exact hPb (Finset.mem_coe.mpr (hBsub (φ L).2)) (Finset.mem_coe.mpr (hBsub (φ L').2))
        (fun h => hne (φ.injective (Subtype.ext h)))
