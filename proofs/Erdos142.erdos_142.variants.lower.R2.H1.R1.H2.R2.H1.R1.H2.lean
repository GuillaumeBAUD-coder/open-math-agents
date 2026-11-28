import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1
import Mathlib

-- Scratch proofs for Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H1.R1.H2 and H3

namespace Scratch37005

open Finset Erdos142

lemma card_le_r3 {N : ℕ} {B : Finset ℕ} (hB : B ⊆ Finset.Icc 1 N)
    (hf : (B : Set ℕ).IsAPOfLengthFree 3) : B.card ≤ r 3 N := by
  unfold r Set.IsAPOfLengthFree.maxCard
  refine le_csSup ?_ ⟨B, hB, hf, rfl⟩
  refine ⟨N, ?_⟩
  rintro _ ⟨U, hU, -, rfl⟩
  simpa using Finset.card_le_card hU

theorem test_37005_H2 :
    ∀ (N q : ℕ) (S : Finset ℕ) (B : Fin q → Finset ℕ),
      S ⊆ Finset.univ.biUnion B →
      (∀ i, B i ⊆ Finset.Icc 1 N ∧ ((B i : Finset ℕ) : Set ℕ).IsAPOfLengthFree 3) →
      S.card ≤ q * r 3 N := by
  intro N q S B hsub hB
  calc S.card
      ≤ (Finset.univ.biUnion B).card := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin q, (B i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin q, r 3 N := Finset.sum_le_sum (fun i _ => card_le_r3 (hB i).1 (hB i).2)
    _ = q * r 3 N := by simp

lemma apFree_iff {A : Set ℕ} {k : ℕ} (hk : 1 < k) :
    A.IsAPOfLengthFree k ↔ ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  constructor
  · rintro hA ⟨a, d, hd, hterms⟩
    let f (i : ℕ) := a + i * d
    let T := (Finset.range k).image f
    have hf : Function.Injective f := fun i j hij =>
      Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
    have hT : ((T : Finset ℕ) : Set ℕ) = {a + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} := by
      ext x
      simp [T, f]
    have hcard : T.card = k := by simp [T, Finset.card_image_of_injective _ hf]
    have hsub : (T : Set ℕ) ⊆ A := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hterms i (Finset.mem_range.mp hi)
    exact hk'.not_ge (hA _ hsub ⟨a, d, by simp [hcard], hT⟩)
  · intro hno T hsub hT
    obtain ⟨a, d, hcard, hterms⟩ := hT
    have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
      rw [hterms]
      exact ⟨i, by exact_mod_cast hi, by simp⟩
    have hd : 0 < d := by
      by_contra! h
      have he : d = 0 := Nat.eq_zero_of_le_zero h
      have hs : T = {a} := by
        apply Set.Subset.antisymm
        · rw [hterms, he]
          rintro _ ⟨i, -, rfl⟩
          simp
        · apply Set.singleton_subset_iff.mpr
          simpa using hmem 0 (by omega)
      rw [hs] at hcard
      exact hk'.ne (by simpa using hcard)
    exact (hno ⟨a, d, hd, fun i hi => hsub (hmem i hi)⟩).elim

lemma exists_large_3ap_free {S : Finset ℕ} (h4 : (S : Set ℕ).IsAPOfLengthFree 4) :
    ∃ B : Finset ℕ, B ⊆ S ∧ (B : Set ℕ).IsAPOfLengthFree 3 ∧ S.card ≤ B.card ^ 2 := by
  classical
  have hno4 := (apFree_iff (by decide : 1 < 4)).mp h4
  let C : Finset (Finset ℕ) := S.powerset.filter (fun B => (B : Set ℕ).IsAPOfLengthFree 3)
  have hne : C.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset S, ?_⟩⟩
    exact (apFree_iff (k := 3) (by decide)).mpr (by rintro ⟨a, d, -, h⟩; simpa using h 0 (by omega))
  obtain ⟨B, hBC, hBmax⟩ := Finset.exists_max_image C Finset.card hne
  have hBS : B ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hBC).1
  have hB3 : (B : Set ℕ).IsAPOfLengthFree 3 := (Finset.mem_filter.mp hBC).2
  have hno3 := (apFree_iff (by decide : 1 < 3)).mp hB3
  refine ⟨B, hBS, hB3, ?_⟩
  -- For each x ∈ S \ B, adding x to B creates a 3-AP, so x is uniquely determined by
  -- a pair (u, v) ∈ B × B with u < v and a bit indicating midpoint vs endpoint.
  let P : Finset (ℕ × ℕ) := (B ×ˢ B).filter (fun p => p.1 < p.2)
  have hPcard : 2 * P.card ≤ B.card * (B.card - 1) := by
    let Q : Finset (ℕ × ℕ) := (B ×ˢ B).filter (fun p => p.2 < p.1)
    have hdisj : Disjoint P Q := by
      rw [Finset.disjoint_left]
      intro p hp hq
      have h1 := (Finset.mem_filter.mp hp).2
      have h2 := (Finset.mem_filter.mp hq).2
      omega
    have hPQcard : Q.card = P.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp
        obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp hp
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩, hlt⟩
      · intro p₁ _ p₂ _ heq
        ext <;> simp_all
      · intro p hp
        obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp hp
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
        exact ⟨(p.2, p.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩, hlt⟩, rfl⟩
    have hsub : P ∪ Q ⊆ B.offDiag := by
      intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp h
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
        exact Finset.mem_offDiag.mpr ⟨h1, h2, by omega⟩
      · obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp h
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
        exact Finset.mem_offDiag.mpr ⟨h1, h2, by omega⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, hPQcard, Finset.offDiag_card] at hle
    have hmul : B.card * B.card - B.card = B.card * (B.card - 1) := by
      cases hc : B.card with
      | zero => simp
      | succ n =>
        change (n + 1) * (n + 1) - (n + 1) = (n + 1) * n
        rw [Nat.mul_add_one, Nat.add_sub_cancel]
    omega
  -- Define the forbidden elements from P × Bool
  -- For each p = (u, v) ∈ P:
  --   false => midpoint (u + v) / 2
  --   true  => whichever of (2 * u - v) or (2 * v - u) lies in S (at most one, since S is 4-AP-free!)
  let f : (ℕ × ℕ) × Bool → ℕ := fun ⟨p, b⟩ =>
    if b then
      if 2 * p.2 - p.1 ∈ S then 2 * p.2 - p.1 else 2 * p.1 - p.2
    else
      (p.1 + p.2) / 2
  have hcover : S \ B ⊆ (P ×ˢ (Finset.univ : Finset Bool)).image f := by
    intro x hx
    obtain ⟨hxS, hxnotB⟩ := Finset.mem_sdiff.mp hx
    have hnotfree : ¬ ((insert x B : Finset ℕ) : Set ℕ).IsAPOfLengthFree 3 := by
      intro hfree'
      have hmemC : insert x B ∈ C := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hfree'⟩
        exact Finset.insert_subset hxS hBS
      have hle := hBmax (insert x B) hmemC
      rw [Finset.card_insert_of_notMem hxnotB] at hle
      omega
    have hnotfree' : ¬ ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 3, a + i * d ∈ ((insert x B : Finset ℕ) : Set ℕ) :=
      fun h => hnotfree ((apFree_iff (k := 3) (by decide)).mpr h)
    push Not at hnotfree'
    obtain ⟨a, d, hd, hterms⟩ := hnotfree'
    have ha := hterms 0 (by omega)
    have hb := hterms 1 (by omega)
    have hc := hterms 2 (by omega)
    simp only [Finset.mem_coe, Finset.mem_insert, zero_mul, add_zero, one_mul] at ha hb hc
    have hnotall : ¬ (a ∈ B ∧ a + d ∈ B ∧ a + 2 * d ∈ B) := by
      rintro ⟨h0, h1, h2⟩
      apply hno3
      refine ⟨a, d, hd, fun i hi => ?_⟩
      interval_cases i
      · simpa using h0
      · simpa using h1
      · simpa using h2
    rcases ha with rfl | haB
    · -- x = a; then a + d ∈ B and a + 2*d ∈ B (since d > 0)
      have h1B : a + d ∈ B := hb.resolve_left (by omega)
      have h2B : a + 2 * d ∈ B := hc.resolve_left (by omega)
      have hpP : (a + d, a + 2 * d) ∈ P :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1B, h2B⟩, by omega⟩
      refine Finset.mem_image.mpr ⟨((a + d, a + 2 * d), true),
        Finset.mem_product.mpr ⟨hpP, Finset.mem_univ true⟩, ?_⟩
      -- Must show 2 * (a + 2*d) - (a + d) ∉ S (else a, a+d, a+2d, a+3d is a 4-AP in S!)
      have h3notS : 2 * (a + 2 * d) - (a + d) ∉ S := by
        intro h3S
        apply hno4
        refine ⟨a, d, hd, fun i hi => ?_⟩
        interval_cases i
        · simpa using hxS
        · simpa using hBS h1B
        · simpa using hBS h2B
        · have heq : a + 3 * d = 2 * (a + 2 * d) - (a + d) := by omega
          simpa [heq] using h3S
      dsimp [f]
      rw [if_neg h3notS]
      omega
    · rcases hb with hxeq | hbB
      · -- x = a + d; a ∈ B and a + 2*d ∈ B
        have h2B : a + 2 * d ∈ B := hc.resolve_left (by omega)
        have hpP : (a, a + 2 * d) ∈ P :=
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haB, h2B⟩, by omega⟩
        refine Finset.mem_image.mpr ⟨((a, a + 2 * d), false),
          Finset.mem_product.mpr ⟨hpP, Finset.mem_univ false⟩, ?_⟩
        dsimp [f]
        omega
      · -- x = a + 2*d; a ∈ B and a + d ∈ B
        have hxeq : x = a + 2 * d := (hc.resolve_right (fun h2B => hnotall ⟨haB, hbB, h2B⟩)).symm
        have hpP : (a, a + d) ∈ P :=
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haB, hbB⟩, by omega⟩
        refine Finset.mem_image.mpr ⟨((a, a + d), true),
          Finset.mem_product.mpr ⟨hpP, Finset.mem_univ true⟩, ?_⟩
        have h3S : 2 * (a + d) - a ∈ S := by
          have heq : 2 * (a + d) - a = x := by omega
          rwa [heq]
        dsimp [f]
        rw [if_pos h3S]
        omega
  have hsdiff : (S \ B).card ≤ 2 * P.card := by
    calc (S \ B).card
        ≤ ((P ×ˢ (Finset.univ : Finset Bool)).image f).card := Finset.card_le_card hcover
      _ ≤ (P ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_image_le
      _ = 2 * P.card := by simp [Finset.card_product, mul_comm]
  have hsum : S.card = B.card + (S \ B).card := by
    have := Finset.card_sdiff_add_card_eq_card hBS
    omega
  have hsq : B.card + B.card * (B.card - 1) = B.card ^ 2 := by
    cases hc : B.card with
    | zero => simp
    | succ n =>
      change (n + 1) + (n + 1) * n = (n + 1) ^ 2
      ring
  omega

lemma cover_4ap_free_strong : ∀ m : ℕ, ∀ (N : ℕ) (S : Finset ℕ),
    S.card = m → S ⊆ Finset.Icc 1 N → (S : Set ℕ).IsAPOfLengthFree 4 →
    ∃ (q : ℕ) (B : Fin q → Finset ℕ),
      S ⊆ Finset.univ.biUnion B ∧
      (∀ i, B i ⊆ Finset.Icc 1 N ∧ ((B i : Finset ℕ) : Set ℕ).IsAPOfLengthFree 3) ∧
      q ^ 2 ≤ 4 * m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro N S hm hS h4
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · refine ⟨0, Fin.elim0, ?_, fun i => Fin.elim0 i, by simp⟩
      have hSe : S = ∅ := Finset.card_eq_zero.mp hm
      simp [hSe]
    · obtain ⟨B0, hB0S, hB03, hB0sq⟩ := exists_large_3ap_free h4
      have hB0pos : 0 < B0.card := by
        by_contra! h
        have h0 : B0.card = 0 := Nat.eq_zero_of_le_zero h
        rw [h0, hm] at hB0sq
        omega
      let S' := S \ B0
      have hB0le : B0.card ≤ m := by
        have := Finset.card_le_card hB0S
        omega
      have hS'card : S'.card = m - B0.card := by
        have h := Finset.card_sdiff_add_card_eq_card hB0S
        change S'.card + B0.card = S.card at h
        omega
      have hS'lt : S'.card < m := by omega
      have hS'4 : (S' : Set ℕ).IsAPOfLengthFree 4 :=
        fun T hT hAP => h4 T (hT.trans (by exact_mod_cast Finset.sdiff_subset)) hAP
      obtain ⟨q', B', hsub', hB', hq'sq⟩ :=
        ih S'.card hS'lt N S' rfl (Finset.sdiff_subset.trans hS) hS'4
      let B : Fin (q' + 1) → Finset ℕ := Fin.cases B0 B'
      refine ⟨q' + 1, B, ?_, ?_, ?_⟩
      · intro x hx
        by_cases hx0 : x ∈ B0
        · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, hx0⟩
        · have hx' : x ∈ S' := Finset.mem_sdiff.mpr ⟨hx, hx0⟩
          obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (hsub' hx')
          exact Finset.mem_biUnion.mpr ⟨i.succ, Finset.mem_univ _, hi⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · exact ⟨hB0S.trans hS, hB03⟩
        · exact hB'
      · have hlt_sq : q' ^ 2 < (2 * B0.card - 1) ^ 2 := by
          have h1 : q' ^ 2 ≤ 4 * (m - B0.card) := by rwa [hS'card] at hq'sq
          have h2 : 4 * (m - B0.card) ≤ 4 * (B0.card ^ 2 - B0.card) := by omega
          have h3 : 4 * (B0.card ^ 2 - B0.card) + 1 = (2 * B0.card - 1) ^ 2 := by
            obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero hB0pos.ne'
            rw [hb]
            have hs1 : (b + 1) ^ 2 - (b + 1) = b * b + b := by
              have : (b + 1) ^ 2 = (b * b + b) + (b + 1) := by ring
              omega
            have hs2 : 2 * (b + 1) - 1 = 2 * b + 1 := by omega
            rw [hs1, hs2]
            ring
          omega
        have hq'lt : q' < 2 * B0.card - 1 := by nlinarith
        have h1 : q' ^ 2 ≤ 4 * (m - B0.card) := by rwa [hS'card] at hq'sq
        have h2b : 1 ≤ 2 * B0.card := by omega
        zify [hB0le, h2b] at h1 hq'lt ⊢
        nlinarith

theorem test_37005_H3 :
    ∀ (N : ℕ) (S : Finset ℕ), S ⊆ Finset.Icc 1 N → (S : Set ℕ).IsAPOfLengthFree 4 → S.card ^ 2 ≤ N →
      ∃ (q : ℕ) (B : Fin q → Finset ℕ),
        S ⊆ Finset.univ.biUnion B ∧
        (∀ i, B i ⊆ Finset.Icc 1 N ∧ ((B i : Finset ℕ) : Set ℕ).IsAPOfLengthFree 3) ∧
        (q : ℝ) ^ 2 * S.card ≤ 4 * N := by
  intro N S hS h4 hsparse
  obtain ⟨q, B, hsub, hB, hqsq⟩ := cover_4ap_free_strong S.card N S rfl hS h4
  refine ⟨q, B, hsub, hB, ?_⟩
  have hnat : q ^ 2 * S.card ≤ 4 * N := by
    calc q ^ 2 * S.card
        ≤ 4 * S.card * S.card := Nat.mul_le_mul_right S.card hqsq
      _ = 4 * S.card ^ 2 := by ring
      _ ≤ 4 * N := Nat.mul_le_mul_left 4 hsparse
  exact_mod_cast hnat

end Scratch37005

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1.H2 := Scratch37005.test_37005_H2
