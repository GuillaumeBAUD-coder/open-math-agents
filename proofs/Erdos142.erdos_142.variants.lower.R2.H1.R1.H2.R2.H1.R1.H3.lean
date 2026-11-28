import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H1.R1.H3
-- Credit: @Carson1903

lemma OMA.isAPOfLengthFree_three_of_no_2b_sub_a {B : Finset ℕ}
    (hB : ∀ a ∈ B, ∀ b ∈ B, a < b → 2 * b - a ∉ B) :
    (B : Set ℕ).IsAPOfLengthFree 3 := by
  intro T hT hAP
  exfalso
  obtain ⟨a, d, hcard, hterms⟩ := hAP
  have hmem : ∀ i < 3, a + i * d ∈ T := by
    intro i hi
    rw [hterms]
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  have hd : 0 < d := by
    by_contra! h
    have hd0 : d = 0 := Nat.eq_zero_of_le_zero h
    have hTs : T = {a} := by
      apply Set.Subset.antisymm
      · rw [hterms, hd0]
        rintro _ ⟨i, -, rfl⟩
        simp
      · exact Set.singleton_subset_iff.mpr (by simpa using hmem 0 (by omega))
    rw [hTs] at hcard
    simp at hcard
  have ha : a ∈ B := hT (by simpa using hmem 0 (by omega))
  have hb : a + d ∈ B := hT (by simpa using hmem 1 (by omega))
  have hc : a + 2 * d ∈ B := hT (by simpa using hmem 2 (by omega))
  have heq : 2 * (a + d) - a = a + 2 * d := by omega
  exact hB a ha (a + d) hb (by omega) (heq.symm ▸ hc)

lemma OMA.greedy_3ap_free_range :
    ∀ (n : ℕ) (T : Finset ℕ), T ⊆ Finset.range n →
      ∃ B ⊆ T,
        (∀ a ∈ B, ∀ b ∈ B, a < b → 2 * b - a ∉ B) ∧
        (∀ x ∈ T, x ∈ B ∨ ∃ a ∈ B, ∃ b ∈ B, a < b ∧ x = 2 * b - a) := by
  intro n
  induction n with
  | zero =>
    intro T hT
    have hTe : T = ∅ := Finset.subset_empty.mp (by simpa using hT)
    subst hTe
    exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  | succ n ih =>
    intro T hT
    have hsub : T.erase n ⊆ Finset.range n := by
      intro x hx
      have hx' := Finset.mem_erase.mp hx
      have hxr := Finset.mem_range.mp (hT hx'.2)
      exact Finset.mem_range.mpr (by omega)
    obtain ⟨B', hB'T, hB'free, hB'cov⟩ := ih (T.erase n) hsub
    have hB'lt : ∀ x ∈ B', x < n := fun x hx ↦ Finset.mem_range.mp (hsub (hB'T hx))
    by_cases hnT : n ∈ T
    · by_cases hforb : ∃ a ∈ B', ∃ b ∈ B', a < b ∧ n = 2 * b - a
      · refine ⟨B', hB'T.trans (Finset.erase_subset _ _), hB'free, ?_⟩
        intro x hx
        by_cases hxn : x = n
        · subst hxn; exact Or.inr hforb
        · exact hB'cov x (Finset.mem_erase.mpr ⟨hxn, hx⟩)
      · refine ⟨insert n B', ?_, ?_, ?_⟩
        · exact Finset.insert_subset hnT (hB'T.trans (Finset.erase_subset _ _))
        · intro a ha b hb hab hmem
          rcases Finset.mem_insert.mp hb with hbn | hb'
          · rw [hbn] at hab hmem
            have hlt : ∀ z ∈ insert n B', z ≤ n := by
              intro z hz
              rcases Finset.mem_insert.mp hz with hzn | hz'
              · exact hzn.le
              · exact (hB'lt z hz').le
            have hle := hlt (2 * n - a) hmem
            omega
          · have ha' : a ∈ B' := by
              rcases Finset.mem_insert.mp ha with rfl | ha'
              · exact absurd hab (not_lt_of_ge (hB'lt b hb').le)
              · exact ha'
            rcases Finset.mem_insert.mp hmem with heq | hmem'
            · exact hforb ⟨a, ha', b, hb', hab, heq.symm⟩
            · exact hB'free a ha' b hb' hab hmem'
        · intro x hx
          by_cases hxn : x = n
          · subst hxn; exact Or.inl (Finset.mem_insert_self _ _)
          · rcases hB'cov x (Finset.mem_erase.mpr ⟨hxn, hx⟩) with hxB | ⟨a, ha, b, hb, hab, rfl⟩
            · exact Or.inl (Finset.mem_insert_of_mem hxB)
            · exact Or.inr ⟨a, Finset.mem_insert_of_mem ha, b, Finset.mem_insert_of_mem hb, hab, rfl⟩
    · have hTeq : T.erase n = T := Finset.erase_eq_of_notMem hnT
      rw [hTeq] at hB'T hB'cov
      exact ⟨B', hB'T, hB'free, hB'cov⟩

lemma OMA.exists_large_3ap_free_subset (T : Finset ℕ) :
    ∃ B ⊆ T, (B : Set ℕ).IsAPOfLengthFree 3 ∧ 2 * T.card ≤ B.card * (B.card + 1) := by
  classical
  let n := T.sup id + 1
  have hTr : T ⊆ Finset.range n := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hx))
  obtain ⟨B, hBT, hBfree, hBcov⟩ := OMA.greedy_3ap_free_range n T hTr
  refine ⟨B, hBT, OMA.isAPOfLengthFree_three_of_no_2b_sub_a hBfree, ?_⟩
  let P := (B ×ˢ B).filter (fun p : ℕ × ℕ ↦ p.1 < p.2)
  let Q := (B ×ˢ B).filter (fun p : ℕ × ℕ ↦ p.2 < p.1)
  have hPQ_disj : Disjoint P Q := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    omega
  have hPQ_sub : P ∪ Q ⊆ (B ×ˢ B).filter (fun p : ℕ × ℕ ↦ p.1 ≠ p.2) := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp1 | hp2
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp1).1, ne_of_lt (Finset.mem_filter.mp hp1).2⟩
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp2).1, ne_of_gt (Finset.mem_filter.mp hp2).2⟩
  have hQ_card : Q.card = P.card := by
    refine Finset.card_bij (fun p _ ↦ (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      obtain ⟨hpBB, hlt⟩ := Finset.mem_filter.mp hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hpBB
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩, hlt⟩
    · intro p1 _ p2 _ heq
      cases p1; cases p2; simp at heq; exact Prod.ext heq.2 heq.1
    · intro p hp
      obtain ⟨hpBB, hlt⟩ := Finset.mem_filter.mp hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hpBB
      exact ⟨(p.2, p.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩, hlt⟩, rfl⟩
  have hdiag : (B ×ˢ B).filter (fun p : ℕ × ℕ ↦ p.1 = p.2) = B.image (fun x ↦ (x, x)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨ha, _⟩, rfl⟩; exact ⟨a, ha, rfl, rfl⟩
    · rintro ⟨x, hx, rfl, rfl⟩; exact ⟨⟨hx, hx⟩, rfl⟩
  have hdiag_card : ((B ×ˢ B).filter (fun p : ℕ × ℕ ↦ p.1 = p.2)).card = B.card := by
    rw [hdiag, Finset.card_image_of_injective]
    intro x y h; simpa using h
  have hsplit := Finset.card_filter_add_card_filter_not (s := B ×ˢ B) (fun p : ℕ × ℕ ↦ p.1 = p.2)
  have hne_card : ((B ×ˢ B).filter (fun p : ℕ × ℕ ↦ p.1 ≠ p.2)).card + B.card = B.card * B.card := by
    have h1 : (B ×ˢ B).filter (fun p : ℕ × ℕ ↦ ¬ p.1 = p.2) =
        (B ×ˢ B).filter (fun p : ℕ × ℕ ↦ p.1 ≠ p.2) := rfl
    rw [hdiag_card, h1, Finset.card_product] at hsplit
    omega
  have h2P : 2 * P.card + B.card ≤ B.card * B.card := by
    have h1 := Finset.card_le_card hPQ_sub
    rw [Finset.card_union_of_disjoint hPQ_disj, hQ_card] at h1
    omega
  have hsdiff_sub : T \ B ⊆ P.image (fun p : ℕ × ℕ ↦ 2 * p.2 - p.1) := by
    intro x hx
    obtain ⟨hxT, hxB⟩ := Finset.mem_sdiff.mp hx
    rcases hBcov x hxT with h | ⟨a, ha, b, hb, hab, rfl⟩
    · exact absurd h hxB
    · exact Finset.mem_image.mpr ⟨(a, b),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩
  have hsdiff_le : (T \ B).card ≤ P.card :=
    (Finset.card_le_card hsdiff_sub).trans Finset.card_image_le
  have hTcard : T.card = (T \ B).card + B.card := by
    rw [Finset.card_sdiff_add_card_eq_card hBT]
  nlinarith

lemma OMA.cover_by_3ap_free :
    ∀ (k : ℕ) (T : Finset ℕ), 2 * T.card ≤ k * (k + 1) →
      ∃ B : Fin k → Finset ℕ,
        T ⊆ Finset.univ.biUnion B ∧
        ∀ i, B i ⊆ T ∧ ((B i : Finset ℕ) : Set ℕ).IsAPOfLengthFree 3 := by
  intro k
  induction k with
  | zero =>
    intro T hT
    have hTe : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hTe
    exact ⟨fun i ↦ Fin.elim0 i, by simp, fun i ↦ Fin.elim0 i⟩
  | succ k ih =>
    intro T hT
    obtain ⟨B0, hB0T, hB0free, hB0card⟩ := OMA.exists_large_3ap_free_subset T
    have hrem_card : (T \ B0).card + B0.card = T.card :=
      Finset.card_sdiff_add_card_eq_card hB0T
    have hrem : 2 * (T \ B0).card ≤ k * (k + 1) := by
      by_cases hb : B0.card ≤ k + 1
      · nlinarith
      · have hb2 : k + 2 ≤ B0.card := by omega
        nlinarith
    obtain ⟨Brest, hrest_cov, hrest_ok⟩ := ih (T \ B0) hrem
    refine ⟨Fin.cons B0 Brest, ?_, ?_⟩
    · intro x hx
      by_cases hx0 : x ∈ B0
      · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, by simpa using hx0⟩
      · have hxr := hrest_cov (Finset.mem_sdiff.mpr ⟨hx, hx0⟩)
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hxr
        exact Finset.mem_biUnion.mpr ⟨i.succ, Finset.mem_univ _, by simpa using hi⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · exact ⟨hB0T, hB0free⟩
      · intro j
        exact ⟨(hrest_ok j).1.trans Finset.sdiff_subset, (hrest_ok j).2⟩

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1.H3 := by
  classical
  intro N S hSN _ hsparse
  have hex : ∃ q : ℕ, 2 * S.card ≤ q * (q + 1) := ⟨2 * S.card, by nlinarith⟩
  let q := Nat.find hex
  have hq_spec : 2 * S.card ≤ q * (q + 1) := Nat.find_spec hex
  obtain ⟨B, hBcov, hBok⟩ := OMA.cover_by_3ap_free q S hq_spec
  refine ⟨q, B, hBcov, fun i ↦ ⟨(hBok i).1.trans hSN, (hBok i).2⟩, ?_⟩
  have hq2 : q ^ 2 ≤ 4 * S.card := by
    by_cases hq0 : q = 0
    · simp [hq0]
    · by_cases hq1 : q = 1
      · have h0 : ¬ (2 * S.card ≤ 0 * (0 + 1)) := Nat.find_min hex (show 0 < q by omega)
        simp only [hq1]; omega
      · have hmin : ¬ (2 * S.card ≤ (q - 1) * ((q - 1) + 1)) :=
          Nat.find_min hex (show q - 1 < q by omega)
        have hlt : (q - 1) * q < 2 * S.card := by
          have : (q - 1) + 1 = q := by omega
          rw [this] at hmin
          omega
        have hq2' : 2 ≤ q := by omega
        obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hq2'
        have hlt' : (1 + m) * (2 + m) < 2 * S.card := by
          rw [hm] at hlt
          simpa [show 2 + m - 1 = 1 + m by omega] using hlt
        rw [hm]
        nlinarith
  have hnat : q ^ 2 * S.card ≤ 4 * N := by
    calc q ^ 2 * S.card
        ≤ (4 * S.card) * S.card := Nat.mul_le_mul_right S.card hq2
      _ = 4 * S.card ^ 2 := by ring
      _ ≤ 4 * N := Nat.mul_le_mul_left 4 hsparse
  exact_mod_cast hnat
