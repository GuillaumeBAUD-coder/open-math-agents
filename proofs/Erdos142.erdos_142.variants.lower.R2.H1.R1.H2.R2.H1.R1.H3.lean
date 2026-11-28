import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H1.R1.H3
-- Credit: @jktcv2kz4f-cyber

namespace Erdos142R2H1R1H2R2H1R1H3

open Finset

private lemma greedy_exists : ∀ (n : ℕ) (S : Finset ℕ), S.card = n →
    ∃ B : Finset ℕ, B ⊆ S ∧ (B : Set ℕ).IsAPOfLengthFree 3 ∧
      (S.Nonempty → B.Nonempty) ∧
      ∀ x ∈ S \ B, ∃ u ∈ B, ∃ v ∈ B, u < v ∧ u + x = 2 * v := by
  classical
  intro n
  induction n with
  | zero =>
    intro S hcard
    have hS : S = ∅ := Finset.card_eq_zero.mp hcard
    subst hS
    refine ⟨∅, Finset.Subset.refl _, ?_, fun h => h, by simp⟩
    intro t ht hap
    have ht0 : t = ∅ := Set.subset_empty_iff.mp (by simpa using ht)
    exact (Set.not_isAPOfLength_empty (by decide : (0 : ℕ∞) < 3) (ht0 ▸ hap)).elim
  | succ n ih =>
    intro S hcard
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    let m : ℕ := S.max' hSne
    have hmS : m ∈ S := Finset.max'_mem S hSne
    let S' : Finset ℕ := S.erase m
    have hS'card : S'.card = n := by
      rw [Finset.card_erase_of_mem hmS, hcard]
      omega
    obtain ⟨B', hB'sub, hB'free, hB'ne, hB'rej⟩ := ih S' hS'card
    have hB'lt : ∀ y ∈ B', y < m := by
      intro y hy
      have hyS' := hB'sub hy
      have hne : y ≠ m := (Finset.mem_erase.mp hyS').1
      have hle : y ≤ m := Finset.le_max' S y (Finset.mem_erase.mp hyS').2
      omega
    by_cases hforb : ∃ u ∈ B', ∃ v ∈ B', u < v ∧ u + m = 2 * v
    · refine ⟨B', hB'sub.trans (Finset.erase_subset m S), hB'free, ?_, ?_⟩
      · intro _
        rcases hforb with ⟨u, hu, _⟩
        exact ⟨u, hu⟩
      · intro x hx
        have hxS : x ∈ S := (Finset.mem_sdiff.mp hx).1
        have hxB : x ∉ B' := (Finset.mem_sdiff.mp hx).2
        by_cases hxm : x = m
        · subst hxm
          exact hforb
        · exact hB'rej x (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hxm, hxS⟩, hxB⟩)
    · let B : Finset ℕ := insert m B'
      have hBsub : B ⊆ S := Finset.insert_subset hmS (hB'sub.trans (Finset.erase_subset m S))
      have hBfree : (B : Set ℕ).IsAPOfLengthFree 3 := by
        intro t ht hap
        rcases hap with ⟨a, d, hc, hteq⟩
        have hmem : ∀ i < 3, a + i * d ∈ B := fun i hi => by
          have hi_t : a + i * d ∈ t := by
            rw [hteq]
            exact ⟨i, by exact_mod_cast hi, by simp⟩
          exact ht hi_t
        have hd : 0 < d := by
          by_contra h0
          have hd0 : d = 0 := by omega
          have hsub1 : t ⊆ ({a} : Set ℕ) := by
            intro z hz
            rw [hteq] at hz
            rcases hz with ⟨i, _, rfl⟩
            simp [hd0]
          have hle : t.encard ≤ ({a} : Set ℕ).encard := Set.encard_le_encard hsub1
          rw [ENat.card_coe_set_eq] at hc
          rw [hc, Set.encard_singleton] at hle
          exact (by decide : ¬ ((3 : ℕ) : ℕ∞) ≤ 1) hle
        have hm0 : a ∈ B := by simpa using hmem 0 (by decide)
        have hm1 : a + d ∈ B := by simpa using hmem 1 (by decide)
        have hm2 : a + 2 * d ∈ B := by simpa using hmem 2 (by decide)
        by_cases h2m : a + 2 * d = m
        · have h0B' : a ∈ B' := by
            rcases Finset.mem_insert.mp hm0 with h | h
            · omega
            · exact h
          have h1B' : a + d ∈ B' := by
            rcases Finset.mem_insert.mp hm1 with h | h
            · omega
            · exact h
          exact (hforb ⟨a, h0B', a + d, h1B', by omega, by omega⟩).elim
        · have h0B' : a ∈ B' := by
            rcases Finset.mem_insert.mp hm0 with h | h
            · have h2le : a + 2 * d ≤ m := Finset.le_max' S _ (hBsub hm2)
              omega
            · exact h
          have h1B' : a + d ∈ B' := by
            rcases Finset.mem_insert.mp hm1 with h | h
            · have h2le : a + 2 * d ≤ m := Finset.le_max' S _ (hBsub hm2)
              omega
            · exact h
          have h2B' : a + 2 * d ∈ B' := (Finset.mem_insert.mp hm2).resolve_left h2m
          have htB' : t ⊆ (B' : Set ℕ) := by
            intro z hz
            rw [hteq] at hz
            rcases hz with ⟨i, hi, rfl⟩
            have hiN : i < 3 := by exact_mod_cast hi
            have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
            rcases hi' with rfl | rfl | rfl
            · simpa using h0B'
            · simpa using h1B'
            · simpa using h2B'
          exact hB'free t htB' ⟨a, d, hc, hteq⟩
      refine ⟨B, hBsub, hBfree, fun _ => ⟨m, Finset.mem_insert_self m B'⟩, ?_⟩
      intro x hx
      have hxS : x ∈ S := (Finset.mem_sdiff.mp hx).1
      have hxB : x ∉ B := (Finset.mem_sdiff.mp hx).2
      have hxm : x ≠ m := fun h => hxB (h ▸ Finset.mem_insert_self m B')
      have hxB' : x ∉ B' := fun h => hxB (Finset.mem_insert_of_mem h)
      obtain ⟨u, hu, v, hv, huv, heq⟩ :=
        hB'rej x (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hxm, hxS⟩, hxB'⟩)
      exact ⟨u, Finset.mem_insert_of_mem hu, v, Finset.mem_insert_of_mem hv, huv, heq⟩

private lemma greedy_card_bound (S : Finset ℕ) (hSne : S.Nonempty) :
    ∃ B : Finset ℕ, B ⊆ S ∧ (B : Set ℕ).IsAPOfLengthFree 3 ∧
      0 < B.card ∧ 2 * S.card ≤ B.card * (B.card + 1) := by
  classical
  obtain ⟨B, hBsub, hBfree, hBne, hBrej⟩ := greedy_exists S.card S rfl
  have hBpos : 0 < B.card := Finset.card_pos.mpr (hBne hSne)
  let P : Finset (ℕ × ℕ) := (B ×ˢ B).filter (fun p => p.1 < p.2)
  let Q : Finset (ℕ × ℕ) := (B ×ˢ B).filter (fun p => p.2 < p.1)
  have hPQdisj : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro p hp hq
    have h1 := (Finset.mem_filter.mp hp).2
    have h2 := (Finset.mem_filter.mp hq).2
    omega
  have hPQsub : P ∪ Q ⊆ B.offDiag := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · have hf := Finset.mem_filter.mp h
      have hprod := Finset.mem_product.mp hf.1
      exact Finset.mem_offDiag.mpr ⟨hprod.1, hprod.2, by omega⟩
    · have hf := Finset.mem_filter.mp h
      have hprod := Finset.mem_product.mp hf.1
      exact Finset.mem_offDiag.mpr ⟨hprod.1, hprod.2, by omega⟩
  have hPeqQ : P.card = Q.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      have hf := Finset.mem_filter.mp hp
      have hprod := Finset.mem_product.mp hf.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hprod.2, hprod.1⟩, hf.2⟩
    · intro p₁ _ p₂ _ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro q hq
      have hf := Finset.mem_filter.mp hq
      have hprod := Finset.mem_product.mp hf.1
      exact ⟨(q.2, q.1),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hprod.2, hprod.1⟩, hf.2⟩, rfl⟩
  have h2P : 2 * P.card ≤ B.card * B.card - B.card := by
    have hu : (P ∪ Q).card = P.card + Q.card := Finset.card_union_of_disjoint hPQdisj
    have hle : (P ∪ Q).card ≤ B.offDiag.card := Finset.card_le_card hPQsub
    rw [Finset.offDiag_card] at hle
    omega
  have hsdiff_sub : S \ B ⊆ P.image (fun p => 2 * p.2 - p.1) := by
    intro x hx
    obtain ⟨u, hu, v, hv, huv, heq⟩ := hBrej x hx
    refine Finset.mem_image.mpr ⟨(u, v), ?_, by omega⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, huv⟩
  have hsdiff_le : (S \ B).card ≤ P.card :=
    (Finset.card_le_card hsdiff_sub).trans Finset.card_image_le
  have hScard : S.card = B.card + (S \ B).card := by
    have := Finset.card_sdiff_add_card_eq_card hBsub
    omega
  have hBsq : B.card ≤ B.card * B.card := Nat.le_mul_self B.card
  refine ⟨B, hBsub, hBfree, hBpos, ?_⟩
  zify [hBsq] at h2P hsdiff_le hScard ⊢
  nlinarith

private lemma cover_3ap_free : ∀ (n : ℕ) (S : Finset ℕ), S.card = n →
    ∃ (q : ℕ) (B : Fin q → Finset ℕ),
      S ⊆ Finset.univ.biUnion B ∧
      (∀ i, B i ⊆ S ∧ ((B i : Finset ℕ) : Set ℕ).IsAPOfLengthFree 3) ∧
      q ^ 2 ≤ 4 * S.card := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hcard
    by_cases h0 : n = 0
    · subst h0
      have hS : S = ∅ := Finset.card_eq_zero.mp hcard
      subst hS
      exact ⟨0, Fin.elim0, by simp, fun i => Fin.elim0 i, by simp⟩
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨B0, hB0sub, hB0free, hB0pos, hB0bound⟩ := greedy_card_bound S hSne
    let S' : Finset ℕ := S \ B0
    have hS'card : S'.card = n - B0.card := by
      have := Finset.card_sdiff_add_card_eq_card hB0sub
      change (S \ B0).card = n - B0.card
      omega
    obtain ⟨q', B', hcover', hprop', hq'bound⟩ := ih S'.card (by omega) S' rfl
    refine ⟨q' + 1, Fin.cons B0 B', ?_, ?_, ?_⟩
    · intro x hx
      by_cases hxB0 : x ∈ B0
      · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hxB0⟩
      · have hxS' : x ∈ S' := Finset.mem_sdiff.mpr ⟨hx, hxB0⟩
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (hcover' hxS')
        exact Finset.mem_biUnion.mpr ⟨i.succ, Finset.mem_univ i.succ, hi⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact ⟨hB0sub, hB0free⟩
      | succ j =>
        exact ⟨(hprop' j).1.trans Finset.sdiff_subset, (hprop' j).2⟩
    · have h4q : 4 * q' ^ 2 ≤ (4 * B0.card - 1) ^ 2 := by
        have h1 : q' ^ 2 ≤ 4 * (n - B0.card) := by rwa [hS'card] at hq'bound
        have h2 : B0.card ≤ n := by
          have := Finset.card_le_card hB0sub
          omega
        have h3 : 2 * n ≤ B0.card * (B0.card + 1) := by rwa [hcard] at hB0bound
        have h4 : 1 ≤ 4 * B0.card := by omega
        zify [h2, h4] at h1 h3 ⊢
        nlinarith
      have h2q : 2 * q' ≤ 4 * B0.card - 1 := by
        have hsq : (2 * q') ^ 2 ≤ (4 * B0.card - 1) ^ 2 := by linarith
        nlinarith
      have h2q1 : 2 * q' + 1 ≤ 4 * B0.card := by omega
      have hle : B0.card ≤ S.card := Finset.card_le_card hB0sub
      have h1 : q' ^ 2 ≤ 4 * (S.card - B0.card) := by
        rw [hS'card, ← hcard] at hq'bound
        exact hq'bound
      zify [hle] at h1 ⊢
      nlinarith

end Erdos142R2H1R1H2R2H1R1H3

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1.H3 := by
  intro N S hS _ hcard_sq
  obtain ⟨q, B, hcov, hprop, hqbound⟩ :=
    Erdos142R2H1R1H2R2H1R1H3.cover_3ap_free S.card S rfl
  refine ⟨q, B, hcov, fun i => ⟨(hprop i).1.trans hS, (hprop i).2⟩, ?_⟩
  have hnat : q ^ 2 * S.card ≤ 4 * N := by
    calc
      q ^ 2 * S.card ≤ (4 * S.card) * S.card := Nat.mul_le_mul_right S.card hqbound
      _ = 4 * S.card ^ 2 := by ring
      _ ≤ 4 * N := Nat.mul_le_mul_left 4 hcard_sq
  exact_mod_cast hnat
