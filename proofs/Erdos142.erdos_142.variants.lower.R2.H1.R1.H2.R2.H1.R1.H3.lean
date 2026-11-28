import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1
import Mathlib

/-! A greedy increasing scan gives a cover of sparse sets by three-AP-free sets. -/

namespace Erdos142SparseCover

open Finset

private def threeFree (B : Finset ℕ) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, a < b → b < c → a + c ≠ 2 * b

private theorem greedy (S : Finset ℕ) :
    ∃ B ⊆ S, threeFree B ∧
      ∀ x ∈ S, x ∉ B → ∃ a ∈ B, ∃ b ∈ B, a < b ∧ b < x ∧ a + x = 2 * b := by
  induction S using Finset.induction_on_max with
  | empty => exact ⟨∅, subset_rfl, by simp [threeFree], by simp⟩
  | insert x S hx ih =>
    obtain ⟨B, hBS, hfree, hskip⟩ := ih
    by_cases h : ∃ a ∈ B, ∃ b ∈ B, a < b ∧ b < x ∧ a + x = 2 * b
    · refine ⟨B, hBS.trans (subset_insert _ _), hfree, ?_⟩
      intro y hy hyB
      rcases mem_insert.mp hy with rfl | hy
      · exact h
      · exact hskip y hy hyB
    · refine ⟨insert x B, insert_subset_insert _ hBS, ?_, ?_⟩
      · intro a ha b hb c hc hab hbc he
        have ha' : a ∈ B := by
          rcases mem_insert.mp ha with rfl | ha
          · rcases mem_insert.mp hb with rfl | hb
            · omega
            · exact ((hx _ (hBS hb)).not_gt hab).elim
          · exact ha
        have hb' : b ∈ B := by
          rcases mem_insert.mp hb with rfl | hb
          · rcases mem_insert.mp hc with rfl | hc
            · omega
            · exact ((hx _ (hBS hc)).not_gt hbc).elim
          · exact hb
        rcases mem_insert.mp hc with rfl | hc
        · exact h ⟨a, ha', b, hb', hab, hbc, he⟩
        · exact hfree a ha' b hb' c hc hab hbc he
      · intro y hy hyB
        have hyS : y ∈ S := (mem_insert.mp hy).resolve_left (fun e => hyB (e ▸ mem_insert_self _ _))
        obtain ⟨a, ha, b, hb, hab, hby, he⟩ :=
          hskip y hyS (fun hy' => hyB (mem_insert_of_mem hy'))
        exact ⟨a, mem_insert_of_mem ha, b, mem_insert_of_mem hb, hab, hby, he⟩

private theorem greedy_size (S : Finset ℕ) :
    ∃ B ⊆ S, threeFree B ∧ S.card ≤ B.card ^ 2 := by
  obtain ⟨B, hBS, hfree, hskip⟩ := greedy S
  let E := B.offDiag.image (fun p => 2 * p.2 - p.1)
  have hsub : S ⊆ B ∪ E := by
    intro x hx
    apply mem_union.mpr
    by_cases hxB : x ∈ B
    · exact Or.inl hxB
    · obtain ⟨a, ha, b, hb, hab, _, he⟩ := hskip x hx hxB
      exact Or.inr (mem_image.mpr ⟨(a, b), mem_offDiag.mpr ⟨ha, hb, hab.ne⟩, by
        dsimp
        omega⟩)
  refine ⟨B, hBS, hfree, ?_⟩
  calc
    S.card ≤ (B ∪ E).card := card_le_card hsub
    _ ≤ B.card + E.card := card_union_le _ _
    _ ≤ B.card + B.offDiag.card := Nat.add_le_add_left card_image_le _
    _ = B.card ^ 2 := by
      rw [offDiag_card, pow_two, Nat.add_sub_of_le]
      exact Nat.le_mul_self _

private theorem cover (S : Finset ℕ) :
    ∃ (q : ℕ) (B : Fin q → Finset ℕ),
      S ⊆ univ.biUnion B ∧ (∀ i, B i ⊆ S ∧ threeFree (B i)) ∧ q ^ 2 ≤ 4 * S.card := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    obtain rfl | hS := S.eq_empty_or_nonempty
    · exact ⟨0, Fin.elim0, empty_subset _, fun i => Fin.elim0 i, by simp⟩
    obtain ⟨A, hAS, hAfree, hAcard⟩ := greedy_size S
    have hApos : 0 < A.card := by
      have hSpos := card_pos.mpr hS
      by_contra! h
      have hzero : S.card ≤ 0 := by
        simpa only [Nat.eq_zero_of_le_zero h, zero_pow (by decide : 2 ≠ 0)] using hAcard
      exact hSpos.not_ge hzero
    obtain ⟨q, B, hcover, hB, hcost⟩ :=
      ih (S \ A) (sdiff_ssubset hAS (card_pos.mp hApos))
    let C : Fin (q + 1) → Finset ℕ := Fin.cases A B
    have hsum : (S \ A).card + A.card = S.card := card_sdiff_add_card_eq_card hAS
    have hq : q < 2 * A.card := by
      by_contra! h
      have hsq := Nat.pow_le_pow_left h 2
      nlinarith
    refine ⟨q + 1, C, ?_, ?_, ?_⟩
    · intro x hx
      by_cases h : x ∈ A
      · exact mem_biUnion.mpr ⟨0, mem_univ _, h⟩
      · obtain ⟨i, _, hi⟩ := mem_biUnion.mp (hcover (mem_sdiff.mpr ⟨hx, h⟩))
        exact mem_biUnion.mpr ⟨i.succ, mem_univ _, hi⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hAS, hAfree⟩
      · exact ⟨(hB j).1.trans sdiff_subset, (hB j).2⟩
    · have hh : 2 * q + 1 ≤ 4 * A.card := by omega
      nlinarith

private theorem isAPOfLengthFree {B : Finset ℕ} (hf : threeFree B) :
    (B : Set ℕ).IsAPOfLengthFree 3 := by
  intro T hsub hT
  obtain ⟨a, d, hc, hT⟩ := hT
  have hd : 0 < d := by
    by_contra! h
    have he : d = 0 := Nat.eq_zero_of_le_zero h
    have hs : T = {a} := by
      rw [hT, he]
      ext x
      constructor
      · rintro ⟨i, -, rfl⟩
        simp
      · intro hx
        obtain rfl := Set.mem_singleton_iff.mp hx
        exact ⟨0, by decide, by simp⟩
    rw [hs] at hc
    norm_num at hc
  have ha : a ∈ B := hsub (hT ▸ ⟨0, by decide, by simp⟩)
  have hb : a + d ∈ B := hsub (hT ▸ ⟨1, by decide, by simp⟩)
  have hc' : a + 2 * d ∈ B := hsub (hT ▸ ⟨2, by decide, by simp⟩)
  exact (hf a ha (a + d) hb (a + 2 * d) hc' (by omega) (by omega) (by omega)).elim

theorem sparse_cover :
    ∀ (N : ℕ) (S : Finset ℕ), S ⊆ Finset.Icc 1 N → (S : Set ℕ).IsAPOfLengthFree 4 → S.card ^ 2 ≤ N →
    ∃ (q : ℕ)(B : Fin q → Finset ℕ),
      S ⊆ Finset.univ.biUnion B ∧
      (∀ i, B i ⊆ Finset.Icc 1 N ∧ ((B i : Finset ℕ) : Set ℕ).IsAPOfLengthFree 3) ∧
      (q : ℝ) ^ 2 * S.card ≤ 4 * N := by
  intro N S hS _ hsparse
  obtain ⟨q, B, hcover, hB, hcost⟩ := cover S
  refine ⟨q, B, hcover, fun i => ⟨(hB i).1.trans hS, isAPOfLengthFree (hB i).2⟩, ?_⟩
  exact_mod_cast (calc
    q ^ 2 * S.card ≤ (4 * S.card) * S.card := Nat.mul_le_mul_right _ hcost
    _ = 4 * S.card ^ 2 := by ring
    _ ≤ 4 * N := Nat.mul_le_mul_left _ hsparse)

end Erdos142SparseCover

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1.H3 :=
  Erdos142SparseCover.sparse_cover
