import OMAStatements.S_mo_167999

private lemma sq_sum_le_card_mul_sum_sq {α : Type*} (s : Finset α) (f : α → ℝ) :
    (∑ x ∈ s, f x) ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, f x ^ 2 := by
  have h : 0 ≤ ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexp : ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 =
      2 * ((s.card : ℝ) * ∑ x ∈ s, f x ^ 2 - (∑ x ∈ s, f x) ^ 2) := by
    simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  linarith

private lemma sumset_cover {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (S T : Finset F) (hcard : Fintype.card F < S.card + T.card) (x : F) :
    ∃ s ∈ S, ∃ t ∈ T, s + t = x := by
  let T' : Finset F := T.image (fun t => x - t)
  have hT' : T'.card = T.card := by
    apply Finset.card_image_of_injective
    intro a b hab
    linear_combination -hab
  have hnd : ¬ Disjoint S T' := by
    intro hdisj
    have hle : (S ∪ T').card ≤ Fintype.card F := Finset.card_le_univ _
    rw [Finset.card_union_of_disjoint hdisj, hT'] at hle
    omega
  obtain ⟨s, hs, hsT'⟩ := Finset.not_disjoint_iff.mp hnd
  obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hsT'
  exact ⟨s, hs, t, ht, by linear_combination -heq⟩

private def splitFin {m : ℕ} {α : Type*} (a₁ a₂ : Fin m → α) (i : Fin (m + m)) : α :=
  if h : (i : ℕ) < m then a₁ ⟨i, h⟩ else a₂ ⟨i - m, by omega⟩

private lemma splitFin_sum {m : ℕ} {F : Type*} [CommRing F]
    (a₁ a₂ g₁ g₂ : Fin m → F) :
    ∑ i : Fin (m + m), splitFin a₁ a₂ i * splitFin g₁ g₂ i =
      ∑ j : Fin m, a₁ j * g₁ j + ∑ j : Fin m, a₂ j * g₂ j := by
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [splitFin, j.isLt]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [splitFin]

private lemma exists_dilate_card_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (S B : Finset F) (hS : 1 ≤ S.card) (hB : 1 ≤ B.card) (hF : 2 ≤ Fintype.card F) :
    ∃ g : F,
      ((S ×ˢ B).image (fun p => p.1 + p.2 * g)).Nonempty ∧
      (Fintype.card F : ℝ) / (((S ×ˢ B).image (fun p => p.1 + p.2 * g)).card : ℝ) ≤
        (Fintype.card F : ℝ) / ((S.card : ℝ) * (B.card : ℝ)) + 1 := by
  let U : Finset F := (Finset.univ : Finset F).erase 0
  have hUcard : U.card = Fintype.card F - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  have hUne : U.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.card_empty] at hUcard
    omega
  let r (g x : F) : ℕ := ((S ×ˢ B).filter (fun p => p.1 + p.2 * g = x)).card
  have hr_sum : ∀ g : F, ∑ x ∈ (S ×ˢ B).image (fun p => p.1 + p.2 * g), (r g x : ℝ) =
      (S.card : ℝ) * (B.card : ℝ) := by
    intro g
    have hnat : ∑ x ∈ (S ×ˢ B).image (fun p => p.1 + p.2 * g), r g x = S.card * B.card := by
      rw [← Finset.card_product]
      symm
      apply Finset.card_eq_sum_card_fiberwise
      intro p hp
      exact Finset.mem_image_of_mem _ hp
    exact_mod_cast hnat
  have hr_sq_sum_eq : ∀ g : F, ∑ x : F, r g x ^ 2 =
      (((S ×ˢ B) ×ˢ (S ×ˢ B)).filter (fun q => q.1.1 + q.1.2 * g = q.2.1 + q.2.2 * g)).card := by
    intro g
    have hsq : ∀ x : F, r g x ^ 2 =
        (((S ×ˢ B) ×ˢ (S ×ˢ B)).filter
          (fun q => q.1.1 + q.1.2 * g = x ∧ q.2.1 + q.2.2 * g = x)).card := by
      intro x
      rw [sq, ← Finset.card_product]
      congr 1
      ext q
      simp only [Finset.mem_product, Finset.mem_filter]
      tauto
    simp_rw [hsq]
    have hfin : ∑ x : F,
        (((S ×ˢ B) ×ˢ (S ×ˢ B)).filter (fun q => q.1.1 + q.1.2 * g = q.2.1 + q.2.2 * g) |>.filter
          (fun q => q.1.1 + q.1.2 * g = x)).card =
        (((S ×ˢ B) ×ˢ (S ×ˢ B)).filter (fun q => q.1.1 + q.1.2 * g = q.2.1 + q.2.2 * g)).card := by
      symm
      apply Finset.card_eq_sum_card_fiberwise
      intro q _
      exact Finset.mem_univ _
    rw [← hfin]
    congr 1
    ext x
    congr 1
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hmem, h1, h2⟩
      exact ⟨⟨hmem, h1.trans h2.symm⟩, h1⟩
    · rintro ⟨⟨hmem, heq⟩, h1⟩
      exact ⟨hmem, h1, heq.symm.trans h1⟩
  have hdouble : ∑ g ∈ U, ∑ x : F, r g x ^ 2 ≤
      S.card * B.card * U.card + (S.card * S.card - S.card) * (B.card * B.card - B.card) := by
    simp_rw [hr_sq_sum_eq, Finset.card_filter]
    rw [Finset.sum_comm]
    have hpt : ∀ q ∈ (S ×ˢ B) ×ˢ (S ×ˢ B),
        (∑ g ∈ U, if q.1.1 + q.1.2 * g = q.2.1 + q.2.2 * g then 1 else 0) ≤
          (if q.1 = q.2 then U.card else 0) +
            (if q.1.1 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2 then 1 else 0) := by
      intro q _
      by_cases h1 : q.1.1 = q.2.1
      · by_cases h2 : q.1.2 = q.2.2
        · have hq : q.1 = q.2 := Prod.ext h1 h2
          simp [hq, h1, h2]
        · have hzero : ∀ g ∈ U, q.1.1 + q.1.2 * g ≠ q.2.1 + q.2.2 * g := by
            intro g hg heq
            have hg0 : g ≠ 0 := (Finset.mem_erase.mp hg).1
            have hmul : (q.1.2 - q.2.2) * g = 0 := by linear_combination heq - h1
            rcases mul_eq_zero.mp hmul with hb | hg'
            · exact h2 (sub_eq_zero.mp hb)
            · exact hg0 hg'
          have hsum0 : (∑ g ∈ U, if q.1.1 + q.1.2 * g = q.2.1 + q.2.2 * g then 1 else 0) = 0 :=
            Finset.sum_eq_zero fun g hg => if_neg (hzero g hg)
          omega
      · by_cases h2 : q.1.2 = q.2.2
        · have hzero : ∀ g ∈ U, q.1.1 + q.1.2 * g ≠ q.2.1 + q.2.2 * g := by
            intro g _ heq
            apply h1
            linear_combination heq - congrArg (· * g) h2
          have hsum0 : (∑ g ∈ U, if q.1.1 + q.1.2 * g = q.2.1 + q.2.2 * g then 1 else 0) = 0 :=
            Finset.sum_eq_zero fun g hg => if_neg (hzero g hg)
          omega
        · have hq : q.1 ≠ q.2 := fun h => h1 (congrArg Prod.fst h)
          have hcard1 : (U.filter (fun g => q.1.1 + q.1.2 * g = q.2.1 + q.2.2 * g)).card ≤ 1 := by
            rw [Finset.card_le_one]
            intro g₁ hg₁ g₂ hg₂
            rw [Finset.mem_filter] at hg₁ hg₂
            have hsub : (q.1.2 - q.2.2) * (g₁ - g₂) = 0 := by
              linear_combination hg₁.2 - hg₂.2
            rcases mul_eq_zero.mp hsub with hb | hg
            · exact absurd (sub_eq_zero.mp hb) h2
            · exact sub_eq_zero.mp hg
          rw [← Finset.card_filter]
          simp only [hq, ↓reduceIte, ne_eq, h1, not_false_eq_true, h2, and_self, zero_add]
          exact hcard1
    calc ∑ q ∈ (S ×ˢ B) ×ˢ (S ×ˢ B), ∑ g ∈ U,
            (if q.1.1 + q.1.2 * g = q.2.1 + q.2.2 * g then 1 else 0)
        ≤ ∑ q ∈ (S ×ˢ B) ×ˢ (S ×ˢ B),
            ((if q.1 = q.2 then U.card else 0) +
              (if q.1.1 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2 then 1 else 0)) :=
          Finset.sum_le_sum hpt
      _ = (∑ q ∈ (S ×ˢ B) ×ˢ (S ×ˢ B), if q.1 = q.2 then U.card else 0) +
            (∑ q ∈ (S ×ˢ B) ×ˢ (S ×ˢ B), if q.1.1 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2 then 1 else 0) :=
          Finset.sum_add_distrib
      _ ≤ S.card * B.card * U.card + (S.card * S.card - S.card) * (B.card * B.card - B.card) := by
          gcongr
          · have hdiag : (∑ q ∈ (S ×ˢ B) ×ˢ (S ×ˢ B), if q.1 = q.2 then U.card else 0) =
                ((S ×ˢ B).card) * U.card := by
              rw [Finset.sum_product]
              have h1 : ∀ p ∈ S ×ˢ B,
                  (∑ q ∈ S ×ˢ B, if p = q then U.card else 0) = U.card := by
                intro p hp
                rw [Finset.sum_ite_eq]
                simp [hp]
              rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul]
            rw [hdiag, Finset.card_product]
          · rw [← Finset.card_filter, ← S.offDiag_card, ← B.offDiag_card, ← Finset.card_product]
            apply Finset.card_le_card_of_injOn (fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2)))
            · intro q hq
              simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq,
                Finset.mem_coe, Finset.mem_offDiag] at hq ⊢
              exact ⟨⟨hq.1.1.1, hq.1.2.1, hq.2.1⟩, ⟨hq.1.1.2, hq.1.2.2, hq.2.2⟩⟩
            · intro q₁ _ q₂ _ h
              cases q₁ with | mk a₁ b₁ =>
              cases q₂ with | mk a₂ b₂ =>
              cases a₁; cases b₁; cases a₂; cases b₂
              simp only [Prod.mk.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := h
              rfl
  obtain ⟨g, hgU, hmin⟩ := U.exists_min_image (fun g => ∑ x : F, r g x ^ 2) hUne
  have hg_avg : U.card * (∑ x : F, r g x ^ 2) ≤
      S.card * B.card * U.card + (S.card * S.card - S.card) * (B.card * B.card - B.card) := by
    calc U.card * (∑ x : F, r g x ^ 2)
        = ∑ _g' ∈ U, ∑ x : F, r g x ^ 2 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ g' ∈ U, ∑ x : F, r g' x ^ 2 := Finset.sum_le_sum fun g' hg' => hmin g' hg'
      _ ≤ S.card * B.card * U.card + (S.card * S.card - S.card) * (B.card * B.card - B.card) :=
          hdouble
  let T : Finset F := (S ×ˢ B).image (fun p => p.1 + p.2 * g)
  have hS_pos : (0 : ℝ) < S.card := by exact_mod_cast hS
  have hB_pos : (0 : ℝ) < B.card := by exact_mod_cast hB
  have hF_pos : (0 : ℝ) < Fintype.card F := by exact_mod_cast lt_of_lt_of_le (by norm_num) hF
  have hU_pos : (0 : ℝ) < U.card := by
    rw [hUcard]
    have : 1 ≤ Fintype.card F - 1 := by omega
    exact_mod_cast this
  have hTne : T.Nonempty := by
    obtain ⟨s, hs⟩ := Finset.card_pos.mp hS
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hB
    exact ⟨s + b * g, Finset.mem_image.mpr ⟨(s, b), Finset.mem_product.mpr ⟨hs, hb⟩, rfl⟩⟩
  have hT_pos : (0 : ℝ) < T.card := by exact_mod_cast hTne.card_pos
  refine ⟨g, hTne, ?_⟩
  have hcs : ((S.card : ℝ) * (B.card : ℝ)) ^ 2 ≤
      (T.card : ℝ) * ∑ x : F, (r g x : ℝ) ^ 2 := by
    have h1 := sq_sum_le_card_mul_sum_sq T (fun x => (r g x : ℝ))
    rw [hr_sum g] at h1
    have h2 : ∑ x ∈ T, (r g x : ℝ) ^ 2 ≤ ∑ x : F, (r g x : ℝ) ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg fun x => sq_nonneg _
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))
  have havgR : (U.card : ℝ) * ∑ x : F, (r g x : ℝ) ^ 2 ≤
      (S.card : ℝ) * (B.card : ℝ) * (U.card : ℝ) +
        ((S.card : ℝ) * (S.card : ℝ) - (S.card : ℝ)) *
          ((B.card : ℝ) * (B.card : ℝ) - (B.card : ℝ)) := by
    have hS_le : S.card ≤ S.card * S.card := Nat.le_mul_self _
    have hB_le : B.card ≤ B.card * B.card := Nat.le_mul_self _
    have hc : ((U.card * ∑ x : F, r g x ^ 2 : ℕ) : ℝ) ≤
        ((S.card * B.card * U.card +
          (S.card * S.card - S.card) * (B.card * B.card - B.card) : ℕ) : ℝ) := by
      exact_mod_cast hg_avg
    push_cast [Nat.cast_sub hS_le, Nat.cast_sub hB_le] at hc
    exact hc
  have hSU : ((S.card : ℝ) - 1) / (U.card : ℝ) ≤ (S.card : ℝ) / (Fintype.card F : ℝ) := by
    rw [hUcard]
    have hle : S.card ≤ Fintype.card F := Finset.card_le_univ S
    have hleR : (S.card : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hle
    have hUcast : ((Fintype.card F - 1 : ℕ) : ℝ) = (Fintype.card F : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card F)]
      norm_num
    rw [hUcast]
    have hU_pos' : 0 < (Fintype.card F : ℝ) - 1 := by rw [← hUcast, ← hUcard]; exact hU_pos
    rw [div_le_div_iff₀ hU_pos' hF_pos]
    nlinarith
  have hsum_bd : ∑ x : F, (r g x : ℝ) ^ 2 ≤
      (S.card : ℝ) * (B.card : ℝ) + ((S.card : ℝ) * (B.card : ℝ)) ^ 2 / (Fintype.card F : ℝ) := by
    have hdiv : ∑ x : F, (r g x : ℝ) ^ 2 ≤
        (S.card : ℝ) * (B.card : ℝ) +
          ((S.card : ℝ) * ((S.card : ℝ) - 1) * ((B.card : ℝ) * ((B.card : ℝ) - 1))) /
            (U.card : ℝ) := by
      have hmul : (U.card : ℝ) * ∑ x : F, (r g x : ℝ) ^ 2 ≤
          (U.card : ℝ) * ((S.card : ℝ) * (B.card : ℝ) +
            (S.card : ℝ) * ((S.card : ℝ) - 1) * ((B.card : ℝ) * ((B.card : ℝ) - 1)) / (U.card : ℝ)) := by
        have heq : (U.card : ℝ) * ((S.card : ℝ) * (B.card : ℝ) +
            (S.card : ℝ) * ((S.card : ℝ) - 1) * ((B.card : ℝ) * ((B.card : ℝ) - 1)) / (U.card : ℝ)) =
            (S.card : ℝ) * (B.card : ℝ) * (U.card : ℝ) +
              (S.card : ℝ) * ((S.card : ℝ) - 1) * ((B.card : ℝ) * ((B.card : ℝ) - 1)) := by
          field_simp
        linarith
      exact le_of_mul_le_mul_left hmul hU_pos
    have hquad : (S.card : ℝ) * ((S.card : ℝ) - 1) * ((B.card : ℝ) * ((B.card : ℝ) - 1)) /
        (U.card : ℝ) ≤ ((S.card : ℝ) * (B.card : ℝ)) ^ 2 / (Fintype.card F : ℝ) := by
      have h1 : (S.card : ℝ) * ((S.card : ℝ) - 1) * ((B.card : ℝ) * ((B.card : ℝ) - 1)) /
          (U.card : ℝ) =
          (S.card : ℝ) * (((S.card : ℝ) - 1) / (U.card : ℝ)) * ((B.card : ℝ) * ((B.card : ℝ) - 1)) := by
        ring
      rw [h1]
      have hB1 : (B.card : ℝ) - 1 ≤ (B.card : ℝ) := by linarith
      have hB0 : 0 ≤ (B.card : ℝ) - 1 := by linarith [show (1 : ℝ) ≤ B.card by exact_mod_cast hB]
      have hSU0 : 0 ≤ ((S.card : ℝ) - 1) / (U.card : ℝ) := by
        apply div_nonneg _ hU_pos.le
        linarith [show (1 : ℝ) ≤ S.card by exact_mod_cast hS]
      calc (S.card : ℝ) * (((S.card : ℝ) - 1) / (U.card : ℝ)) * ((B.card : ℝ) * ((B.card : ℝ) - 1))
          ≤ (S.card : ℝ) * ((S.card : ℝ) / (Fintype.card F : ℝ)) * ((B.card : ℝ) * (B.card : ℝ)) := by
            gcongr
        _ = ((S.card : ℝ) * (B.card : ℝ)) ^ 2 / (Fintype.card F : ℝ) := by ring
    linarith
  have hcs2 : ((S.card : ℝ) * (B.card : ℝ)) ^ 2 ≤
      (T.card : ℝ) * ((S.card : ℝ) * (B.card : ℝ) +
        ((S.card : ℝ) * (B.card : ℝ)) ^ 2 / (Fintype.card F : ℝ)) :=
    hcs.trans (mul_le_mul_of_nonneg_left hsum_bd (Nat.cast_nonneg _))
  have hSB_pos : 0 < (S.card : ℝ) * (B.card : ℝ) := mul_pos hS_pos hB_pos
  rw [div_le_iff₀ hT_pos]
  have hmul : ((S.card : ℝ) * (B.card : ℝ)) ^ 2 / (Fintype.card F : ℝ) * (Fintype.card F : ℝ) ≤
      ((S.card : ℝ) * (B.card : ℝ)) ^ 2 / (Fintype.card F : ℝ) *
        (((Fintype.card F : ℝ) / ((S.card : ℝ) * (B.card : ℝ)) + 1) * (T.card : ℝ)) := by
    have hl : ((S.card : ℝ) * (B.card : ℝ)) ^ 2 / (Fintype.card F : ℝ) * (Fintype.card F : ℝ) =
        ((S.card : ℝ) * (B.card : ℝ)) ^ 2 := by field_simp
    have hr : ((S.card : ℝ) * (B.card : ℝ)) ^ 2 / (Fintype.card F : ℝ) *
        (((Fintype.card F : ℝ) / ((S.card : ℝ) * (B.card : ℝ)) + 1) * (T.card : ℝ)) =
        (T.card : ℝ) * ((S.card : ℝ) * (B.card : ℝ) +
          ((S.card : ℝ) * (B.card : ℝ)) ^ 2 / (Fintype.card F : ℝ)) := by field_simp
    rw [hl, hr]
    exact hcs2
  exact le_of_mul_le_mul_left hmul (div_pos (sq_pos_of_pos hSB_pos) hF_pos)

private lemma inductive_dilate_seq {F : Type*} [Field F] [Fintype F]
    (B : Finset F) (hB : 3 ≤ B.card) (hBsym : ∀ x ∈ B, -x ∈ B) (k : ℕ) :
    ∃ (g : Fin (k + 1) → F) (S : Finset F),
      S.Nonempty ∧
      (∀ x ∈ S, -x ∈ S) ∧
      (∀ x ∈ S, ∃ a : Fin (k + 1) → F, (∀ i, a i ∈ B) ∧ (∑ i, a i * g i) = x) ∧
      (Fintype.card F : ℝ) / (S.card : ℝ) ≤
        (Fintype.card F : ℝ) / (B.card : ℝ) ^ (k + 1) + 3 / 2 := by
  classical
  have hF : 2 ≤ Fintype.card F := le_trans (by norm_num) (le_trans hB (Finset.card_le_univ B))
  induction k with
  | zero =>
    refine ⟨fun _ => 1, B, Finset.card_pos.mp (by omega), hBsym, ?_, ?_⟩
    · intro x hx
      refine ⟨fun _ => x, fun _ => hx, ?_⟩
      simp
    · rw [pow_one]
      linarith
  | succ k ih =>
    obtain ⟨g, S, hSne, hSsym, hSrep, hSbd⟩ := ih
    obtain ⟨g_new, hTne, hTbd⟩ := exists_dilate_card_bound S B hSne.card_pos (by omega) hF
    refine ⟨Fin.snoc g g_new, (S ×ˢ B).image (fun p => p.1 + p.2 * g_new), hTne, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨⟨s, b⟩, hsb, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_product] at hsb
      refine Finset.mem_image.mpr ⟨(-s, -b), Finset.mem_product.mpr ⟨hSsym s hsb.1, hBsym b hsb.2⟩, ?_⟩
      ring
    · intro x hx
      obtain ⟨⟨s, b⟩, hsb, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_product] at hsb
      obtain ⟨a, haB, hasum⟩ := hSrep s hsb.1
      refine ⟨Fin.snoc a b, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa using hsb.2
        · intro j
          simpa using haB j
      · rw [Fin.sum_univ_castSucc]
        simp [Fin.snoc_castSucc, Fin.snoc_last, hasum]
    · have hB_pos : (0 : ℝ) < B.card := by exact_mod_cast (by omega : 0 < B.card)
      have hB3 : (3 : ℝ) ≤ B.card := by exact_mod_cast hB
      calc (Fintype.card F : ℝ) / (((S ×ˢ B).image (fun p => p.1 + p.2 * g_new)).card : ℝ)
          ≤ (Fintype.card F : ℝ) / ((S.card : ℝ) * (B.card : ℝ)) + 1 := hTbd
        _ = ((Fintype.card F : ℝ) / (S.card : ℝ)) / (B.card : ℝ) + 1 := by ring
        _ ≤ ((Fintype.card F : ℝ) / (B.card : ℝ) ^ (k + 1) + 3 / 2) / (B.card : ℝ) + 1 := by
            gcongr
        _ = (Fintype.card F : ℝ) / (B.card : ℝ) ^ (k + 2) + (3 / 2) / (B.card : ℝ) + 1 := by
            rw [pow_succ']
            ring
        _ ≤ (Fintype.card F : ℝ) / (B.card : ℝ) ^ (k + 2) + (3 / 2) / 3 + 1 := by
            gcongr
        _ = (Fintype.card F : ℝ) / (B.card : ℝ) ^ (k + 2) + 3 / 2 := by ring

private lemma solve_ge_three {F : Type*} [Field F] [Fintype F]
    (B : Finset F) (hB : 3 ≤ B.card) (hBsym : ∀ x ∈ B, -x ∈ B) :
    ∃ (n : ℕ) (g : Fin n → F),
      (n : ℝ) ≤ 6 * Real.log (Fintype.card F : ℝ) / Real.log (B.card : ℝ) ∧
        ∀ x : F, ∃ a : Fin n → F, (∀ i, a i ∈ B) ∧ (∑ i, a i * g i) = x := by
  classical
  let k : ℕ := Nat.log B.card (2 * Fintype.card F)
  obtain ⟨g, S, hSne, _, hSrep, hSbd⟩ := inductive_dilate_seq B hB hBsym k
  have hF_le : B.card ≤ Fintype.card F := Finset.card_le_univ B
  have hF3 : 3 ≤ Fintype.card F := le_trans hB hF_le
  have hpow_gt : 2 * Fintype.card F < B.card ^ (k + 1) :=
    Nat.lt_pow_succ_log_self (by omega) _
  have hpow_gtR : (2 : ℝ) * (Fintype.card F : ℝ) < (B.card : ℝ) ^ (k + 1) := by
    exact_mod_cast hpow_gt
  have hpow_pos : (0 : ℝ) < (B.card : ℝ) ^ (k + 1) := by
    positivity
  have hF_div_lt : (Fintype.card F : ℝ) / (B.card : ℝ) ^ (k + 1) < 1 / 2 := by
    rw [div_lt_iff₀ hpow_pos]
    linarith
  have hS_div_lt : (Fintype.card F : ℝ) / (S.card : ℝ) < 2 := by linarith
  have hS_pos : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  rw [div_lt_iff₀ hS_pos] at hS_div_lt
  have hScard_gt : Fintype.card F < S.card + S.card := by
    have : (Fintype.card F : ℝ) < (S.card : ℝ) + (S.card : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨k + 1 + (k + 1), splitFin g g, ?_, ?_⟩
  · have hpow_le : B.card ^ k ≤ 2 * Fintype.card F :=
      Nat.pow_log_le_self B.card (by omega)
    have hpow_leR : (B.card : ℝ) ^ k ≤ 2 * (Fintype.card F : ℝ) := by exact_mod_cast hpow_le
    have hB_posR : (0 : ℝ) < B.card := by exact_mod_cast (by omega : 0 < B.card)
    have hB_gt1 : (1 : ℝ) < B.card := by exact_mod_cast (by omega : 1 < B.card)
    have hlogB_pos : 0 < Real.log (B.card : ℝ) := Real.log_pos hB_gt1
    have hlog_pow : Real.log ((B.card : ℝ) ^ k) ≤ Real.log (2 * (Fintype.card F : ℝ)) :=
      Real.log_le_log (pow_pos hB_posR k) hpow_leR
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at hlog_pow
    have hlog2_le : Real.log 2 ≤ Real.log (Fintype.card F : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ Fintype.card F))
    have hlogB_le : Real.log (B.card : ℝ) ≤ Real.log (Fintype.card F : ℝ) :=
      Real.log_le_log hB_posR (by exact_mod_cast hF_le)
    have hk_le : (k : ℝ) ≤ 2 * (Real.log (Fintype.card F : ℝ) / Real.log (B.card : ℝ)) := by
      rw [← mul_div_assoc, le_div_iff₀ hlogB_pos]
      linarith
    have h1_le : (1 : ℝ) ≤ Real.log (Fintype.card F : ℝ) / Real.log (B.card : ℝ) := by
      rw [le_div_iff₀ hlogB_pos, one_mul]
      exact hlogB_le
    calc ((k + 1 + (k + 1) : ℕ) : ℝ) = 2 * (k : ℝ) + 2 * 1 := by push_cast; ring
      _ ≤ 2 * (2 * (Real.log (Fintype.card F : ℝ) / Real.log (B.card : ℝ))) +
            2 * (Real.log (Fintype.card F : ℝ) / Real.log (B.card : ℝ)) := by gcongr
      _ = 6 * Real.log (Fintype.card F : ℝ) / Real.log (B.card : ℝ) := by ring
  · intro x
    obtain ⟨s₁, hs₁, s₂, hs₂, hsum⟩ := sumset_cover S S hScard_gt x
    obtain ⟨a₁, ha₁, rfl⟩ := hSrep s₁ hs₁
    obtain ⟨a₂, ha₂, rfl⟩ := hSrep s₂ hs₂
    refine ⟨splitFin a₁ a₂, ?_, ?_⟩
    · intro i
      dsimp [splitFin]
      split_ifs
      · exact ha₁ _
      · exact ha₂ _
    · rw [splitFin_sum, hsum]

theorem OMA.solution : type_of% @OMA.S_mo_167999.main := by
  classical
  refine ⟨12, by norm_num, ?_⟩
  intro F _ _ A hA hAsym
  have hA_le_F : A.card ≤ Fintype.card F := Finset.card_le_univ A
  by_cases hF2 : Fintype.card F = 2
  · have hA2 : A.card = Fintype.card F := by omega
    have hAuniv : A = Finset.univ := Finset.eq_univ_of_card A hA2
    refine ⟨1, fun _ => 1, ?_, ?_⟩
    · have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hAcard2 : A.card = 2 := by omega
      rw [hF2, hAcard2]
      push_cast
      rw [mul_div_assoc, div_self hlog2_pos.ne', mul_one]
      norm_num
    · intro x
      refine ⟨fun _ => x, fun _ => hAuniv ▸ Finset.mem_univ x, ?_⟩
      simp
  · by_cases hA3 : 3 ≤ A.card
    · obtain ⟨n, g, hn, hrep⟩ := solve_ge_three A hA3 hAsym
      refine ⟨n, g, ?_, hrep⟩
      have hlogA_pos : 0 < Real.log (A.card : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < A.card))
      have hlogF_nn : 0 ≤ Real.log (Fintype.card F : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Fintype.card F))
      calc (n : ℝ) ≤ 6 * Real.log (Fintype.card F : ℝ) / Real.log (A.card : ℝ) := hn
        _ ≤ 12 * Real.log (Fintype.card F : ℝ) / Real.log (A.card : ℝ) := by gcongr; norm_num
    · have hF3 : 3 ≤ Fintype.card F := by omega
      have hA2 : A.card = 2 := by omega
      have h01 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
      have hex_g : ∃ g₀ : F, g₀ ∉ ({0, 1} : Finset F) := by
        by_contra h
        push Not at h
        have hsub : Finset.univ ⊆ ({0, 1} : Finset F) := fun x _ => h x
        have hle := Finset.card_le_card hsub
        rw [Finset.card_univ] at hle
        omega
      obtain ⟨g₀, hg₀⟩ := hex_g
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hg₀
      obtain ⟨hg0, hg1⟩ := hg₀
      let B : Finset F := (A ×ˢ A).image (fun p => p.1 + p.2 * g₀)
      have hBsym : ∀ x ∈ B, -x ∈ B := by
        intro x hx
        obtain ⟨⟨a₁, a₂⟩, ha, rfl⟩ := Finset.mem_image.mp hx
        rw [Finset.mem_product] at ha
        refine Finset.mem_image.mpr ⟨(-a₁, -a₂), Finset.mem_product.mpr ⟨hAsym a₁ ha.1, hAsym a₂ ha.2⟩, ?_⟩
        ring
      have hB3 : 3 ≤ B.card := by
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
        let s : Finset F := {a + a * g₀, a + b * g₀, b + a * g₀}
        have hs_sub : s ⊆ B := by
          intro x hx
          dsimp only [s, B] at hx ⊢
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact Finset.mem_image.mpr ⟨(a, a), Finset.mem_product.mpr ⟨ha, ha⟩, rfl⟩
          · exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
          · exact Finset.mem_image.mpr ⟨(b, a), Finset.mem_product.mpr ⟨hb, ha⟩, rfl⟩
        have hne12 : a + a * g₀ ≠ a + b * g₀ := by
          intro h
          have hmul : (a - b) * g₀ = 0 := by linear_combination h
          rcases mul_eq_zero.mp hmul with h1 | h2
          · exact hab (sub_eq_zero.mp h1)
          · exact hg0 h2
        have hne13 : a + a * g₀ ≠ b + a * g₀ := by
          intro h
          exact hab (by linear_combination h)
        have hne23 : a + b * g₀ ≠ b + a * g₀ := by
          intro h
          have hmul : (a - b) * (1 - g₀) = 0 := by linear_combination h
          rcases mul_eq_zero.mp hmul with h1 | h2
          · exact hab (sub_eq_zero.mp h1)
          · exact hg1 (sub_eq_zero.mp h2).symm
        have hscard : s.card = 3 := by
          simp only [s]
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simpa using hne23
          · simp [hne12, hne13]
        calc 3 = s.card := hscard.symm
          _ ≤ B.card := Finset.card_le_card hs_sub
      obtain ⟨m, h, hm, hrep⟩ := solve_ge_three B hB3 hBsym
      refine ⟨m + m, splitFin h (fun j => g₀ * h j), ?_, ?_⟩
      · have hlogA_pos : 0 < Real.log (A.card : ℝ) :=
          Real.log_pos (by exact_mod_cast (by omega : 1 < A.card))
        have hlogB_pos : 0 < Real.log (B.card : ℝ) :=
          Real.log_pos (by exact_mod_cast (by omega : 1 < B.card))
        have hlogA_le_B : Real.log (A.card : ℝ) ≤ Real.log (B.card : ℝ) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < A.card))
            (by exact_mod_cast (by omega : A.card ≤ B.card))
        have hlogF_nn : 0 ≤ Real.log (Fintype.card F : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Fintype.card F))
        calc ((m + m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
          _ ≤ 2 * (6 * Real.log (Fintype.card F : ℝ) / Real.log (B.card : ℝ)) := by gcongr
          _ = 12 * Real.log (Fintype.card F : ℝ) / Real.log (B.card : ℝ) := by ring
          _ ≤ 12 * Real.log (Fintype.card F : ℝ) / Real.log (A.card : ℝ) := by gcongr
      · intro x
        obtain ⟨b, hbB, hbx⟩ := hrep x
        have hex : ∀ j : Fin m, ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ + a₂ * g₀ = b j := by
          intro j
          obtain ⟨⟨a₁, a₂⟩, ha, heq⟩ := Finset.mem_image.mp (hbB j)
          rw [Finset.mem_product] at ha
          exact ⟨a₁, ha.1, a₂, ha.2, heq⟩
        choose a₁ ha₁ a₂ ha₂ hbe using hex
        refine ⟨splitFin a₁ a₂, ?_, ?_⟩
        · intro i
          dsimp [splitFin]
          split_ifs
          · exact ha₁ _
          · exact ha₂ _
        · rw [splitFin_sum]
          calc ∑ j : Fin m, a₁ j * h j + ∑ j : Fin m, a₂ j * (g₀ * h j)
              = ∑ j : Fin m, (a₁ j + a₂ j * g₀) * h j := by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun j _ => ?_
                ring
            _ = ∑ j : Fin m, b j * h j := by
                refine Finset.sum_congr rfl fun j _ => by rw [hbe j]
            _ = x := hbx
