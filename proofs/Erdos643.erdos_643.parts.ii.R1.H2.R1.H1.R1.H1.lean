import OMAReductions.R_Erdos643_erdos_643_parts_ii_R1_H2_R1_H1_R1
import Mathlib

/-!
# Erdős 643: local starification with a linear edge budget

An elementary proof of Lemma 2.1 of Huang, Ma and Yang (arXiv:2609.37744) in the weak form
needed here: deleting an `ε`-fraction of the edges suffices. The Hilton–Milner and Frankl
bounds of the paper are replaced by counting the `k`-sets that contain a fixed small set,
and every `n^δ` parameter by a constant.
-/

namespace OMA_E643LS

open Finset

variable {n : ℕ}

/-! ## Counting supersets -/

lemma card_supersets_le (k : ℕ) (T : Finset (Fin n)) :
    ((univ.powersetCard k).filter (fun S : Finset (Fin n) => T ⊆ S)).card ≤
      n ^ (k - T.card) := by
  classical
  calc ((univ.powersetCard k).filter (fun S : Finset (Fin n) => T ⊆ S)).card
      ≤ (univ.powersetCard (k - T.card) : Finset (Finset (Fin n))).card := by
        apply card_le_card_of_injOn (fun S => S \ T)
        · intro S hS
          rw [mem_coe, mem_filter, mem_powersetCard] at hS
          rw [mem_coe, mem_powersetCard]
          refine ⟨subset_univ _, ?_⟩
          rw [card_sdiff_of_subset hS.2, hS.1.2]
        · intro S hS S' hS' h
          rw [mem_coe, mem_filter, mem_powersetCard] at hS hS'
          have h' : S \ T = S' \ T := h
          rw [← sdiff_union_of_subset hS.2, ← sdiff_union_of_subset hS'.2, h']
    _ = n.choose (k - T.card) := by simp
    _ ≤ n ^ (k - T.card) := Nat.choose_le_pow _ _

/-- A family of `k`-sets, each containing one of the sets `f i` (`i ∈ I`), all of size `p`. -/
lemma card_le_cover {ι : Type*} (A : Finset (Finset (Fin n))) (k p : ℕ) (I : Finset ι)
    (f : ι → Finset (Fin n)) (hf : ∀ i ∈ I, (f i).card = p)
    (hA : ∀ S ∈ A, S.card = k ∧ ∃ i ∈ I, f i ⊆ S) :
    A.card ≤ I.card * n ^ (k - p) := by
  classical
  calc A.card ≤ (I.biUnion (fun i =>
        (univ.powersetCard k).filter (fun S : Finset (Fin n) => f i ⊆ S))).card := by
        apply card_le_card
        intro S hS
        obtain ⟨hk, i, hi, hsub⟩ := hA S hS
        simp only [mem_biUnion, mem_filter, mem_powersetCard, subset_univ, true_and]
        exact ⟨i, hi, hk, hsub⟩
    _ ≤ ∑ i ∈ I, ((univ.powersetCard k).filter (fun S : Finset (Fin n) => f i ⊆ S)).card :=
        card_biUnion_le
    _ ≤ ∑ _i ∈ I, n ^ (k - p) := by
        apply sum_le_sum
        intro i hi
        have := card_supersets_le k (f i)
        rwa [hf i hi] at this
    _ = I.card * n ^ (k - p) := by simp

lemma card_three {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset (Fin n)).card = 3 := by
  rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]

/-! ## Intersecting families in which every vertex misses many members -/

lemma abc_lemma {k U : ℕ} (v0 : Fin n) (A : Finset (Finset (Fin n)))
    (hcard : ∀ S ∈ A, S.card = k)
    (hint : ∀ S ∈ A, ∀ S' ∈ A, (S ∩ S').Nonempty)
    (hne : A.Nonempty)
    (hns : ¬ ∃ v, ∀ S ∈ A, v ∈ S)
    (hmiss : ∀ v, U ≤ (A.filter (fun S => v ∉ S)).card)
    (hU : k ^ 3 * n ^ (k - 3) < U) :
    ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ∀ S ∈ A, (a ∈ S ∧ b ∈ S) ∨ (a ∈ S ∧ c ∈ S) ∨ (b ∈ S ∧ c ∈ S) := by
  classical
  have hk2 : k ^ 2 * n ^ (k - 3) ≤ k ^ 3 * n ^ (k - 3) := by
    apply Nat.mul_le_mul_right
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h]
    · exact Nat.pow_le_pow_right h (by norm_num)
  have hk1 : k * n ^ (k - 3) ≤ k ^ 3 * n ^ (k - 3) := by
    apply Nat.mul_le_mul_right
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h]
    · simpa using Nat.pow_le_pow_right h (show 1 ≤ 3 by norm_num)
  push_neg at hns
  -- every subfamily that some vertex misses has at least `U` members
  have hbig : ∀ B : Finset (Finset (Fin n)), (∃ v, A.filter (fun S => v ∉ S) ⊆ B) →
      U ≤ B.card := fun B ⟨v, hv⟩ => (hmiss v).trans (card_le_card hv)
  have hAbig : U ≤ A.card := hbig A ⟨v0, filter_subset _ _⟩
  -- Step 1: a cover of size two
  have hcover : ∃ a b, ∀ S ∈ A, a ∈ S ∨ b ∈ S := by
    by_contra h2
    push_neg at h2
    obtain ⟨A1, hA1⟩ := hne
    choose! A2 hA2 using hns
    choose! A3 hA3 using h2
    let I : Finset (Fin n × Fin n × Fin n) := A1.biUnion (fun a => (A2 a).biUnion
      (fun b => (A3 a b).image (fun c => (a, b, c))))
    have hI : I.card ≤ k ^ 3 := by
      calc I.card ≤ ∑ a ∈ A1, ((A2 a).biUnion
            (fun b => (A3 a b).image (fun c => (a, b, c)))).card := card_biUnion_le
        _ ≤ ∑ _a ∈ A1, k * k := by
            apply sum_le_sum
            intro a ha
            calc ((A2 a).biUnion (fun b => (A3 a b).image (fun c => (a, b, c)))).card
                ≤ ∑ b ∈ A2 a, ((A3 a b).image (fun c => (a, b, c))).card := card_biUnion_le
              _ ≤ ∑ _b ∈ A2 a, k := by
                  apply sum_le_sum
                  intro b hb
                  exact card_image_le.trans (hcard _ (hA3 a b).1).le
              _ = k * k := by simp [hcard _ (hA2 a).1]
        _ = k ^ 3 := by simp [hcard _ hA1]; ring
    have hle : A.card ≤ I.card * n ^ (k - 3) := by
      apply card_le_cover A k 3 I (fun x => {x.1, x.2.1, x.2.2})
      · intro x hx
        simp only [I, mem_biUnion, mem_image] at hx
        obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hx
        have hba : b ≠ a := fun h => (hA2 a).2 (h ▸ hb)
        have hca : c ≠ a := fun h => (hA3 a b).2.1 (h ▸ hc)
        have hcb : c ≠ b := fun h => (hA3 a b).2.2 (h ▸ hc)
        exact card_three hba.symm hca.symm hcb.symm
      · intro S hS
        refine ⟨hcard S hS, ?_⟩
        obtain ⟨a, ha⟩ := hint S hS A1 hA1
        obtain ⟨b, hb⟩ := hint S hS (A2 a) (hA2 a).1
        obtain ⟨c, hc⟩ := hint S hS (A3 a b) (hA3 a b).1
        rw [mem_inter] at ha hb hc
        refine ⟨(a, b, c), ?_, ?_⟩
        · simp only [I, mem_biUnion, mem_image]
          exact ⟨a, ha.2, b, hb.2, c, hc.2, rfl⟩
        · intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          exacts [ha.1, hb.1, hc.1]
    have := hle.trans (Nat.mul_le_mul_right _ hI)
    omega
  obtain ⟨a, b, hab⟩ := hcover
  have hab' : a ≠ b := by
    rintro rfl
    obtain ⟨S, hS, haS⟩ := hns a
    rcases hab S hS with h | h <;> exact haS h
  -- the two sides of the cover
  set Aa := A.filter (fun S => b ∉ S) with hAa
  set Ab := A.filter (fun S => a ∉ S) with hAb
  have hAa_big : U ≤ Aa.card := hmiss b
  have hAb_big : U ≤ Ab.card := hmiss a
  have hAa_a : ∀ S ∈ Aa, a ∈ S := by
    intro S hS
    rw [hAa, mem_filter] at hS
    exact (hab S hS.1).resolve_right hS.2
  have hAb_b : ∀ S ∈ Ab, b ∈ S := by
    intro S hS
    rw [hAb, mem_filter] at hS
    exact (hab S hS.1).resolve_left hS.2
  -- Step 2: the members of `Aa` meet outside `a`
  have hAa_int : ∀ S1 ∈ Aa, ∀ S2 ∈ Aa, ((S1.erase a) ∩ (S2.erase a)).Nonempty := by
    intro S1 hS1 S2 hS2
    by_contra hdis
    rw [not_nonempty_iff_eq_empty] at hdis
    have hle : Ab.card ≤ ((S1.erase a) ×ˢ (S2.erase a)).card * n ^ (k - 3) := by
      apply card_le_cover Ab k 3 _ (fun x => {b, x.1, x.2})
      · intro x hx
        rw [mem_product] at hx
        have hb1 : b ≠ x.1 := by
          rintro h
          have := (mem_filter.1 hS1).2
          exact this (h ▸ mem_of_mem_erase hx.1)
        have hb2 : b ≠ x.2 := by
          rintro h
          have := (mem_filter.1 hS2).2
          exact this (h ▸ mem_of_mem_erase hx.2)
        have h12 : x.1 ≠ x.2 := by
          intro h
          have : x.1 ∈ (S1.erase a) ∩ (S2.erase a) := mem_inter.2 ⟨hx.1, h ▸ hx.2⟩
          rw [hdis] at this
          exact absurd this (notMem_empty _)
        exact card_three hb1 hb2 h12
      · intro T hT
        have hTA : T ∈ A := (mem_filter.1 hT).1
        have haT : a ∉ T := (mem_filter.1 hT).2
        refine ⟨hcard T hTA, ?_⟩
        obtain ⟨s1, hs1⟩ := hint T hTA S1 (mem_filter.1 hS1).1
        obtain ⟨s2, hs2⟩ := hint T hTA S2 (mem_filter.1 hS2).1
        rw [mem_inter] at hs1 hs2
        have hs1a : s1 ≠ a := fun h => haT (h ▸ hs1.1)
        have hs2a : s2 ≠ a := fun h => haT (h ▸ hs2.1)
        refine ⟨(s1, s2), mem_product.2 ⟨mem_erase.2 ⟨hs1a, hs1.2⟩,
          mem_erase.2 ⟨hs2a, hs2.2⟩⟩, ?_⟩
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        exacts [hAb_b T hT, hs1.1, hs2.1]
    have hc : ((S1.erase a) ×ˢ (S2.erase a)).card ≤ k ^ 2 := by
      rw [card_product]
      have h1 := card_erase_le (s := S1) (a := a)
      have h2 := card_erase_le (s := S2) (a := a)
      rw [hcard S1 (mem_filter.1 hS1).1] at h1
      rw [hcard S2 (mem_filter.1 hS2).1] at h2
      calc _ ≤ k * k := Nat.mul_le_mul h1 h2
        _ = k ^ 2 := by ring
    have := hle.trans (Nat.mul_le_mul_right _ hc)
    omega
  -- Step 3: the members of `Aa` share a vertex `c ≠ a`
  have hAa_ne : Aa.Nonempty := by
    rw [← card_pos]
    have : 0 < U := lt_of_le_of_lt (Nat.zero_le _) hU
    omega
  have hcex : ∃ c, c ≠ a ∧ ∀ S ∈ Aa, c ∈ S := by
    by_contra hno
    push_neg at hno
    choose! S2 hS2 using hno
    obtain ⟨S1, hS1⟩ := hAa_ne
    let I : Finset (Fin n × Fin n) := (S1.erase a).biUnion
      (fun s => ((S2 s).erase a).image (fun s' => (s, s')))
    have hI : I.card ≤ k ^ 2 := by
      calc I.card ≤ ∑ s ∈ S1.erase a, (((S2 s).erase a).image (fun s' => (s, s'))).card :=
            card_biUnion_le
        _ ≤ ∑ _s ∈ S1.erase a, k := by
            apply sum_le_sum
            intro s hs
            have hsa : s ≠ a := (mem_erase.1 hs).1
            calc _ ≤ ((S2 s).erase a).card := card_image_le
              _ ≤ (S2 s).card := card_erase_le
              _ = k := hcard _ (mem_filter.1 (hS2 s hsa).1).1
        _ ≤ k * k := by
            rw [sum_const, smul_eq_mul]
            apply Nat.mul_le_mul_right
            calc _ ≤ S1.card := card_erase_le
              _ = k := hcard _ (mem_filter.1 hS1).1
        _ = k ^ 2 := by ring
    have hle : Aa.card ≤ I.card * n ^ (k - 3) := by
      apply card_le_cover Aa k 3 I (fun x => {a, x.1, x.2})
      · intro x hx
        simp only [I, mem_biUnion, mem_image] at hx
        obtain ⟨s, hs, s', hs', rfl⟩ := hx
        have hsa : s ≠ a := (mem_erase.1 hs).1
        have hs'a : s' ≠ a := (mem_erase.1 hs').1
        have hss' : s ≠ s' := by
          rintro rfl
          exact (hS2 s hsa).2 (mem_of_mem_erase hs')
        exact card_three hsa.symm hs'a.symm hss'
      · intro S hS
        refine ⟨hcard S (mem_filter.1 hS).1, ?_⟩
        obtain ⟨s, hs⟩ := hAa_int S hS S1 hS1
        rw [mem_inter] at hs
        have hsa : s ≠ a := (mem_erase.1 hs.1).1
        obtain ⟨s', hs'⟩ := hAa_int S hS (S2 s) (hS2 s hsa).1
        rw [mem_inter] at hs'
        refine ⟨(s, s'), ?_, ?_⟩
        · simp only [I, mem_biUnion, mem_image]
          exact ⟨s, hs.2, s', hs'.2, rfl⟩
        · intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          exacts [hAa_a S hS, mem_of_mem_erase hs.1, mem_of_mem_erase hs'.1]
    have := hle.trans (Nat.mul_le_mul_right _ hI)
    omega
  obtain ⟨c, hca, hcAa⟩ := hcex
  have hcb : c ≠ b := by
    rintro rfl
    obtain ⟨S1, hS1⟩ := hAa_ne
    exact (mem_filter.1 hS1).2 (hcAa S1 hS1)
  -- Step 4: the members of `Ab` contain `c`
  have hcAb : ∀ T ∈ Ab, c ∈ T := by
    by_contra hno
    push_neg at hno
    obtain ⟨T0, hT0, hcT0⟩ := hno
    have haT0 : a ∉ T0 := (mem_filter.1 hT0).2
    have hle : Aa.card ≤ T0.card * n ^ (k - 3) := by
      apply card_le_cover Aa k 3 T0 (fun s => {a, c, s})
      · intro s hs
        have hsa : s ≠ a := fun h => haT0 (h ▸ hs)
        have hsc : s ≠ c := fun h => hcT0 (h ▸ hs)
        exact card_three hca.symm hsa.symm hsc.symm
      · intro S hS
        refine ⟨hcard S (mem_filter.1 hS).1, ?_⟩
        obtain ⟨s, hs⟩ := hint S (mem_filter.1 hS).1 T0 (mem_filter.1 hT0).1
        rw [mem_inter] at hs
        refine ⟨s, hs.2, ?_⟩
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        exacts [hAa_a S hS, hcAa S hS, hs.1]
    rw [hcard T0 (mem_filter.1 hT0).1] at hle
    omega
  refine ⟨a, b, c, hab', hca.symm, hcb.symm, ?_⟩
  intro S hS
  by_cases haS : a ∈ S
  · by_cases hbS : b ∈ S
    · exact Or.inl ⟨haS, hbS⟩
    · exact Or.inr (Or.inl ⟨haS, hcAa S (mem_filter.2 ⟨hS, hbS⟩)⟩)
  · have hbS : b ∈ S := (hab S hS).resolve_left haS
    exact Or.inr (Or.inr ⟨hbS, hcAb S (mem_filter.2 ⟨hS, haS⟩)⟩)


/-! ## Many pairs with two disjoint common links -/

/-- The pairs `(u, v)` having two disjoint common links `P`, `Q` in `R`. -/
def GoodPair (R : Finset (Finset (Fin n))) (u v : Fin n) : Prop :=
  ∃ P Q : Finset (Fin n), Disjoint P Q ∧ u ∉ P ∧ v ∉ P ∧ u ∉ Q ∧ v ∉ Q ∧
    insert u P ∈ R ∧ insert v P ∈ R ∧ insert u Q ∈ R ∧ insert v Q ∈ R

open scoped Classical in
lemma good_pairs {m q : ℕ} (hn : 0 < n) (hm : 1 ≤ m) (R : Finset (Finset (Fin n)))
    (hR : ∀ S ∈ R, S.card = m) (hRc : q * n ^ (m - 1) ≤ R.card) :
    q ^ 2 ≤ (univ.offDiag.filter (fun p : Fin n × Fin n => GoodPair R p.1 p.2)).card + m * n := by
  set Pc : Finset (Finset (Fin n)) := univ.powersetCard (m - 1) with hPc
  set Nb : Finset (Fin n) → Finset (Fin n) :=
    fun P => univ.filter (fun u => u ∉ P ∧ insert u P ∈ R) with hNb
  set good := univ.offDiag.filter (fun p : Fin n × Fin n => GoodPair R p.1 p.2) with hgood
  set O : Finset (Fin n × Fin n) := univ.offDiag with hO
  have hPccard : Pc.card ≤ n ^ (m - 1) := by
    rw [hPc, card_powersetCard, card_univ, Fintype.card_fin]
    exact Nat.choose_le_pow _ _
  -- (1) `|R| ≤ ∑ d`
  have hsum_ge : R.card ≤ ∑ P ∈ Pc, (Nb P).card := by
    rw [← card_sigma]
    have hne : ∀ S ∈ R, S.Nonempty := fun S hS => by
      rw [← card_pos, hR S hS]; omega
    apply card_le_card_of_injOn (fun S => if h : S.Nonempty then
      (⟨S.erase h.choose, h.choose⟩ : Σ _ : Finset (Fin n), Fin n) else ⟨∅, ⟨0, hn⟩⟩)
    · intro S hS
      have hS' : S ∈ R := hS
      simp only [dif_pos (hne S hS'), coe_sigma, Set.mem_sigma_iff, mem_coe, hPc, hNb,
        mem_powersetCard, subset_univ, true_and, mem_filter, mem_univ]
      have hc := (hne S hS').choose_spec
      refine ⟨?_, notMem_erase _ _, ?_⟩
      · rw [card_erase_of_mem hc, hR S hS']
      · rw [insert_erase hc]; exact hS'
    · intro S hS S' hS' h
      have hS1 : S ∈ R := hS
      have hS1' : S' ∈ R := hS'
      simp only [dif_pos (hne S hS1), dif_pos (hne S' hS1')] at h
      rw [Sigma.mk.inj_iff] at h
      obtain ⟨h1, h2⟩ := h
      have h2' : (hne S hS1).choose = (hne S' hS1').choose := eq_of_heq h2
      rw [← insert_erase (hne S hS1).choose_spec, ← insert_erase (hne S' hS1').choose_spec,
        h1, h2']
  -- (2) `∑ d ≤ n ^ m`
  have hsum_le : ∑ P ∈ Pc, (Nb P).card ≤ n ^ (m - 1) * n := by
    calc ∑ P ∈ Pc, (Nb P).card ≤ ∑ _P ∈ Pc, n := by
          apply sum_le_sum
          intro P _
          calc (Nb P).card ≤ (univ : Finset (Fin n)).card := card_le_card (subset_univ _)
            _ = n := by simp
      _ = Pc.card * n := by simp
      _ ≤ n ^ (m - 1) * n := Nat.mul_le_mul_right _ hPccard
  -- (3) Cauchy–Schwarz
  have hCS : (∑ P ∈ Pc, (Nb P).card) ^ 2 ≤ Pc.card * ∑ P ∈ Pc, (Nb P).card ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  -- (4) `d² = |offDiag| + d`
  have hsq : ∀ P, (Nb P).card ^ 2 = ((Nb P).offDiag).card + (Nb P).card := by
    intro P
    rw [offDiag_card, sq]
    have : (Nb P).card ≤ (Nb P).card * (Nb P).card := Nat.le_mul_self _
    omega
  -- (5) double counting of `(P, (u, v))`
  set cd : Fin n × Fin n → ℕ := fun p => (Pc.filter (fun P => p ∈ (Nb P).offDiag)).card
    with hcd
  have hswap : ∑ P ∈ Pc, ((Nb P).offDiag).card = ∑ p ∈ O, cd p := by
    have h1 : ∀ P ∈ Pc, ((Nb P).offDiag).card = ∑ p ∈ O, if p ∈ (Nb P).offDiag then 1 else 0 := by
      intro P _
      rw [← card_filter]
      congr 1
      ext p
      constructor
      · intro h
        exact mem_filter.2 ⟨by rw [hO, mem_offDiag]; exact ⟨mem_univ _, mem_univ _,
          (mem_offDiag.1 h).2.2⟩, h⟩
      · intro h
        exact (mem_filter.1 h).2
    rw [sum_congr rfl h1, sum_comm]
    apply sum_congr rfl
    intro p _
    simp only [hcd, card_filter]
  -- (6) bounds on `cd`
  have hcd_good : ∀ p ∈ good, cd p ≤ n ^ (m - 1) := fun p _ =>
    (card_le_card (filter_subset _ _)).trans hPccard
  have hcd_bad : ∀ p ∈ O.filter (fun p => ¬ GoodPair R p.1 p.2),
      cd p ≤ (m - 1) * n ^ (m - 2) := by
    intro p hp
    rw [mem_filter] at hp
    set Cp := Pc.filter (fun P => p ∈ (Nb P).offDiag) with hCp
    have hmemCp : ∀ P ∈ Cp, P.card = m - 1 ∧ p.1 ∉ P ∧ insert p.1 P ∈ R ∧
        p.2 ∉ P ∧ insert p.2 P ∈ R := by
      intro P hP
      simp only [hCp, mem_filter, hPc, mem_powersetCard, subset_univ, true_and, mem_offDiag,
        hNb, mem_univ] at hP
      exact ⟨hP.1, hP.2.1.1, hP.2.1.2, hP.2.2.1.1, hP.2.2.1.2⟩
    have hint : ∀ P ∈ Cp, ∀ Q ∈ Cp, (P ∩ Q).Nonempty := by
      intro P hP Q hQ
      by_contra hdis
      rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hdis
      obtain ⟨_, h1P, h1R, h2P, h2R⟩ := hmemCp P hP
      obtain ⟨_, h1Q, h1R', h2Q, h2R'⟩ := hmemCp Q hQ
      exact hp.2 ⟨P, Q, hdis, h1P, h2P, h1Q, h2Q, h1R, h2R, h1R', h2R'⟩
    change Cp.card ≤ _
    rcases Cp.eq_empty_or_nonempty with he | ⟨P0, hP0⟩
    · rw [he]; simp
    · obtain ⟨hP0c, -⟩ := hmemCp P0 hP0
      have := card_le_cover Cp (m - 1) 1 P0 (fun z => {z}) (fun _ _ => card_singleton _)
        (fun P hP => ⟨(hmemCp P hP).1, by
          obtain ⟨z, hz⟩ := hint P hP P0 hP0
          rw [mem_inter] at hz
          exact ⟨z, hz.2, singleton_subset_iff.2 hz.1⟩⟩)
      rw [hP0c] at this
      simpa [Nat.sub_sub] using this
  have hsplit : ∑ p ∈ O, cd p ≤ good.card * n ^ (m - 1) + (m - 1) * n ^ m := by
    rw [← sum_filter_add_sum_filter_not O (fun p => GoodPair R p.1 p.2)]
    apply add_le_add
    · calc _ ≤ ∑ _p ∈ good, n ^ (m - 1) := sum_le_sum hcd_good
        _ = good.card * n ^ (m - 1) := by simp
    · calc _ ≤ ∑ _p ∈ O.filter (fun p => ¬ GoodPair R p.1 p.2), (m - 1) * n ^ (m - 2) :=
            sum_le_sum hcd_bad
        _ ≤ O.card * ((m - 1) * n ^ (m - 2)) := by
            rw [sum_const, smul_eq_mul]
            exact Nat.mul_le_mul_right _ (card_le_card (filter_subset _ _))
        _ ≤ (n * n) * ((m - 1) * n ^ (m - 2)) := by
            apply Nat.mul_le_mul_right
            rw [hO, offDiag_card, card_univ, Fintype.card_fin]
            exact Nat.sub_le _ _
        _ ≤ (m - 1) * n ^ m := by
            rcases Nat.lt_or_ge m 2 with h | h
            · have : m - 1 = 0 := by omega
              simp [this]
            · have : n ^ m = n * n * n ^ (m - 2) := by
                rw [← pow_two, ← pow_add]; congr 1; omega
              rw [this]; ring_nf; exact le_refl _
  -- (7) combine
  have hn1 : 0 < n ^ (m - 1) := pow_pos hn _
  have key : q ^ 2 * (n ^ (m - 1) * n ^ (m - 1)) ≤
      (good.card + m * n) * (n ^ (m - 1) * n ^ (m - 1)) := by
    calc q ^ 2 * (n ^ (m - 1) * n ^ (m - 1)) = (q * n ^ (m - 1)) ^ 2 := by ring
      _ ≤ R.card ^ 2 := Nat.pow_le_pow_left hRc 2
      _ ≤ (∑ P ∈ Pc, (Nb P).card) ^ 2 := Nat.pow_le_pow_left hsum_ge 2
      _ ≤ Pc.card * ∑ P ∈ Pc, (Nb P).card ^ 2 := hCS
      _ ≤ n ^ (m - 1) * ∑ P ∈ Pc, (Nb P).card ^ 2 := Nat.mul_le_mul_right _ hPccard
      _ = n ^ (m - 1) * (∑ p ∈ O, cd p + ∑ P ∈ Pc, (Nb P).card) := by
          rw [sum_congr rfl (fun P _ => hsq P), sum_add_distrib, hswap]
      _ ≤ n ^ (m - 1) * (good.card * n ^ (m - 1) + (m - 1) * n ^ m + n ^ (m - 1) * n) := by
          apply Nat.mul_le_mul_left
          exact add_le_add hsplit hsum_le
      _ = (good.card + m * n) * (n ^ (m - 1) * n ^ (m - 1)) := by
          have : n ^ m = n ^ (m - 1) * n := by
            rw [← pow_succ]; congr 1; omega
          rw [this]
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
  exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos hn1 hn1)

/-! ## Common neighbourhoods and the non-star count -/

/-- The common link `CN(x, y)` of a `t`-graph: `(t-1)`-sets completing both `x` and `y`. -/
def CN (t : ℕ) (G : Finset (Finset (Fin n))) (x y : Fin n) : Finset (Finset (Fin n)) :=
  (univ.powersetCard (t - 1)).filter
    (fun S => x ∉ S ∧ y ∉ S ∧ insert x S ∈ G ∧ insert y S ∈ G)

/-- A star: some vertex lies in every member (the empty family is a star). -/
def Star (A : Finset (Finset (Fin n))) : Prop := ∃ v, ∀ S ∈ A, v ∈ S

open scoped Classical in
/-- The number of ordered pairs whose common link is not a star. -/
noncomputable def NS (t : ℕ) (G : Finset (Finset (Fin n))) : ℕ :=
  (univ.offDiag.filter (fun p : Fin n × Fin n => ¬ Star (CN t G p.1 p.2))).card

lemma mem_CN {t : ℕ} {G : Finset (Finset (Fin n))} {x y : Fin n} {S : Finset (Fin n)} :
    S ∈ CN t G x y ↔ S.card = t - 1 ∧ x ∉ S ∧ y ∉ S ∧ insert x S ∈ G ∧ insert y S ∈ G := by
  simp [CN, mem_powersetCard]

lemma CN_mono {t : ℕ} {G G' : Finset (Finset (Fin n))} (h : G' ⊆ G) (x y : Fin n) :
    CN t G' x y ⊆ CN t G x y := by
  intro S hS
  rw [mem_CN] at hS ⊢
  exact ⟨hS.1, hS.2.1, hS.2.2.1, h hS.2.2.2.1, h hS.2.2.2.2⟩

lemma star_mono {A A' : Finset (Finset (Fin n))} (h : A' ⊆ A) (hA : Star A) : Star A' := by
  obtain ⟨v, hv⟩ := hA
  exact ⟨v, fun S hS => hv S (h hS)⟩

open scoped Classical in
lemma NS_add_le {t : ℕ} {G G' : Finset (Finset (Fin n))} (h : G' ⊆ G)
    (Q : Finset (Fin n × Fin n))
    (hQ : ∀ p ∈ Q, p.1 ≠ p.2 ∧ ¬ Star (CN t G p.1 p.2) ∧ Star (CN t G' p.1 p.2)) :
    NS t G' + Q.card ≤ NS t G := by
  unfold NS
  rw [← card_union_of_disjoint]
  · apply card_le_card
    intro p hp
    rw [mem_union] at hp
    simp only [mem_filter, mem_offDiag, mem_univ, true_and] at hp ⊢
    rcases hp with hp | hp
    · exact ⟨hp.1, fun hs => hp.2 (star_mono (CN_mono h _ _) hs)⟩
    · exact ⟨(hQ p hp).1, (hQ p hp).2.1⟩
  · rw [disjoint_left]
    intro p hp hpQ
    simp only [mem_filter] at hp
    exact hp.2 (hQ p hpQ).2.2

open scoped Classical in
lemma NS_le_sq (t : ℕ) (G : Finset (Finset (Fin n))) : NS t G ≤ n * n := by
  unfold NS
  calc _ ≤ (univ.offDiag : Finset (Fin n × Fin n)).card := card_le_card (filter_subset _ _)
    _ ≤ n * n := by rw [offDiag_card, card_univ, Fintype.card_fin]; exact Nat.sub_le _ _

lemma hasRDU_mono {G F : Finset (Finset (Fin n))} (h : G ⊆ F) :
    G.HasRepeatedDisjointUnion → F.HasRepeatedDisjointUnion := by
  rintro ⟨A, hA, B, hB, C, hC, D, hD, rest⟩
  exact ⟨A, h hA, B, h hB, C, h hC, D, h hD, rest⟩

/-- Avoiding repeated disjoint unions makes every common link intersecting. -/
lemma CN_intersecting {t : ℕ} (ht : 2 ≤ t) {F G : Finset (Finset (Fin n))} (hGF : G ⊆ F)
    (hF : ¬ F.HasRepeatedDisjointUnion) {x y : Fin n} (hxy : x ≠ y)
    {S S' : Finset (Fin n)} (hS : S ∈ CN t G x y) (hS' : S' ∈ CN t G x y) :
    (S ∩ S').Nonempty := by
  rw [mem_CN] at hS hS'
  obtain ⟨hSc, hxS, hyS, hxSG, hySG⟩ := hS
  obtain ⟨hSc', hxS', hyS', hxSG', hySG'⟩ := hS'
  by_contra hdis
  rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hdis
  have hSne : S.Nonempty := by rw [← card_pos, hSc]; omega
  have hSS' : S ≠ S' := by
    rintro rfl
    obtain ⟨z, hz⟩ := hSne
    exact disjoint_left.1 hdis hz hz
  have hins : ∀ {a : Fin n} {T T' : Finset (Fin n)}, a ∉ T → a ∉ T' →
      insert a T = insert a T' → T = T' := by
    intro a T T' haT haT' h
    rw [← erase_insert haT, ← erase_insert haT', h]
  apply hF
  refine ⟨insert x S, hGF hxSG, insert y S', hGF hySG', insert y S, hGF hySG,
    insert x S', hGF hxSG', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [disjoint_left]
    intro z hz1 hz2
    rw [mem_insert] at hz1 hz2
    rcases hz1 with rfl | hz1 <;> rcases hz2 with h2 | hz2
    · exact hxy h2
    · exact hxS' hz2
    · exact hyS (h2 ▸ hz1)
    · exact disjoint_left.1 hdis hz1 hz2
  · rw [disjoint_left]
    intro z hz1 hz2
    rw [mem_insert] at hz1 hz2
    rcases hz1 with rfl | hz1 <;> rcases hz2 with h2 | hz2
    · exact hxy h2.symm
    · exact hyS' hz2
    · exact hxS (h2 ▸ hz1)
    · exact disjoint_left.1 hdis hz1 hz2
  · ext z; simp only [mem_union, mem_insert]; tauto
  · intro h
    have : x ∈ insert y S' := h ▸ mem_insert_self x S
    rw [mem_insert] at this
    rcases this with h1 | h1
    exacts [hxy h1, hxS' h1]
  · intro h
    have : y ∈ insert x S' := h ▸ mem_insert_self y S
    rw [mem_insert] at this
    rcases this with h1 | h1
    exacts [hxy h1.symm, hyS' h1]
  · intro h
    have : x ∈ insert y S := h ▸ mem_insert_self x S
    rw [mem_insert] at this
    rcases this with h1 | h1
    exacts [hxy h1, hxS h1]
  · exact fun h => hSS' (hins hxS hxS' h)
  · exact fun h => hSS' (hins hyS' hyS h).symm
  · intro h
    have : y ∈ insert x S' := h ▸ mem_insert_self y S'
    rw [mem_insert] at this
    rcases this with h1 | h1
    exacts [hxy h1.symm, hyS' h1]

/-! ## The minimal subfamily -/

section Minimal

variable {t U B : ℕ} {F G : Finset (Finset (Fin n))}

/-- Deleting fewer than `U * j` edges cannot turn `j` non-star pairs into stars. -/
lemma no_cheap_improvement
    (hP : F.card + U * NS t G ≤ G.card + B)
    (hmin : ∀ G' ⊆ G, F.card + U * NS t G' ≤ G'.card + B → G.card ≤ G'.card)
    {G' : Finset (Finset (Fin n))} (hG' : G' ⊆ G) {j : ℕ} (hj : 1 ≤ j)
    (hNS : NS t G' + j ≤ NS t G) (hcost : G.card < G'.card + U * j) : False := by
  have hP' : F.card + U * NS t G' ≤ G'.card + B := by
    have h1 : U * NS t G' + U * j ≤ U * NS t G := by
      rw [← mul_add]; exact Nat.mul_le_mul_left _ hNS
    omega
  have hle := hmin G' hG' hP'
  have hne : G' ≠ G := by
    rintro rfl
    omega
  have := card_lt_card (ssubset_of_subset_of_ne hG' hne)
  omega

open scoped Classical in
/-- In the minimal subfamily, every vertex misses at least `U` members of a non-star link. -/
lemma miss_ge
    (hP : F.card + U * NS t G ≤ G.card + B)
    (hmin : ∀ G' ⊆ G, F.card + U * NS t G' ≤ G'.card + B → G.card ≤ G'.card)
    {x y : Fin n} (hxy : x ≠ y) (hns : ¬ Star (CN t G x y)) (v : Fin n) :
    U ≤ ((CN t G x y).filter (fun S => v ∉ S)).card := by
  by_contra hlt
  push_neg at hlt
  set Dl := ((CN t G x y).filter (fun S => v ∉ S)).image (insert x) with hDl
  set G' := G \ Dl with hG'
  have hG'G : G' ⊆ G := sdiff_subset
  have hstar : Star (CN t G' x y) := by
    refine ⟨v, fun S hS => ?_⟩
    by_contra hvS
    have hSG : S ∈ CN t G x y := CN_mono hG'G x y hS
    rw [mem_CN] at hS
    have : insert x S ∈ Dl := mem_image.2 ⟨S, mem_filter.2 ⟨hSG, hvS⟩, rfl⟩
    exact (mem_sdiff.1 hS.2.2.2.1).2 this
  have hNS : NS t G' + 1 ≤ NS t G := by
    have := NS_add_le hG'G {(x, y)} (by
      intro p hp
      rw [mem_singleton] at hp
      subst hp
      exact ⟨hxy, hns, hstar⟩)
    simpa using this
  have hcost : G.card < G'.card + U * 1 := by
    have h1 : G.card ≤ G'.card + Dl.card := by
      rw [hG']
      have := card_sdiff_add_card_inter G Dl
      have h2 : (G ∩ Dl).card ≤ Dl.card := card_le_card inter_subset_right
      omega
    have h2 : Dl.card < U := lt_of_le_of_lt card_image_le hlt
    omega
  exact no_cheap_improvement hP hmin hG'G le_rfl hNS hcost

/-- Root sets: `2 |S ∩ R| > |R|` for every member `S` of the link. -/
lemma rt_exists (ht : 4 ≤ t) (hn : 0 < n) (hF : ¬ F.HasRepeatedDisjointUnion) (hGF : G ⊆ F)
    (hP : F.card + U * NS t G ≤ G.card + B)
    (hmin : ∀ G' ⊆ G, F.card + U * NS t G' ≤ G'.card + B → G.card ≤ G'.card)
    (hU : (t - 1) ^ 3 * n ^ (t - 4) < U) (p : Fin n × Fin n) :
    ∃ R : Finset (Fin n), R.card ≤ 3 ∧
      (p.1 ≠ p.2 → ∀ S ∈ CN t G p.1 p.2, R.card < 2 * (S ∩ R).card) := by
  classical
  by_cases hp : p.1 = p.2
  · exact ⟨∅, by simp, fun h => absurd hp h⟩
  by_cases hs : Star (CN t G p.1 p.2)
  · obtain ⟨v, hv⟩ := hs
    refine ⟨{v}, by simp, fun _ S hS => ?_⟩
    have : S ∩ {v} = {v} := by
      rw [inter_singleton_of_mem (hv S hS)]
    rw [this]; simp
  · have hne : (CN t G p.1 p.2).Nonempty := by
      rw [nonempty_iff_ne_empty]
      rintro he
      exact hs ⟨⟨0, hn⟩, by simp [he]⟩
    obtain ⟨a, b, c, hab, hac, hbc, habc⟩ := abc_lemma (k := t - 1) (U := U) ⟨0, hn⟩ (CN t G p.1 p.2)
      (fun S hS => (mem_CN.1 hS).1)
      (fun S hS S' hS' => CN_intersecting (by omega) hGF hF hp hS hS')
      hne hs (miss_ge hP hmin hp hs)
      (by have : t - 1 - 3 = t - 4 := by omega
          rw [this]; exact hU)
    refine ⟨{a, b, c}, by rw [card_three hab hac hbc], fun _ S hS => ?_⟩
    rw [card_three hab hac hbc]
    have h2 : 2 ≤ (S ∩ {a, b, c}).card := by
      rcases habc S hS with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · calc 2 = ({a, b} : Finset (Fin n)).card := (card_pair hab).symm
          _ ≤ _ := card_le_card (by intro z hz; simp at hz; rcases hz with rfl | rfl <;> simp_all)
      · calc 2 = ({a, c} : Finset (Fin n)).card := (card_pair hac).symm
          _ ≤ _ := card_le_card (by intro z hz; simp at hz; rcases hz with rfl | rfl <;> simp_all)
      · calc 2 = ({b, c} : Finset (Fin n)).card := (card_pair hbc).symm
          _ ≤ _ := card_le_card (by intro z hz; simp at hz; rcases hz with rfl | rfl <;> simp_all)
    omega

end Minimal

lemma inter_nonempty_of_rt {M1 M2 R : Finset (Fin n)} (h1 : R.card < 2 * (M1 ∩ R).card)
    (h2 : R.card < 2 * (M2 ∩ R).card) : ∃ z, z ∈ M1 ∧ z ∈ M2 ∧ z ∈ R := by
  classical
  obtain ⟨z, hz⟩ : ((M1 ∩ R) ∩ (M2 ∩ R)).Nonempty := by
    rw [← card_pos]
    have h := card_union_add_card_inter (M1 ∩ R) (M2 ∩ R)
    have hu : ((M1 ∩ R) ∪ (M2 ∩ R)).card ≤ R.card :=
      card_le_card (union_subset inter_subset_right inter_subset_right)
    omega
  simp only [mem_inter] at hz
  exact ⟨z, hz.1.1, hz.2.1, hz.1.2⟩

/-- A root set of a non-star link has exactly three elements, each member containing two. -/
lemma rt_card_three {t : ℕ} {G : Finset (Finset (Fin n))} {x y : Fin n}
    (hns : ¬ Star (CN t G x y)) {R : Finset (Fin n)} (hR3 : R.card ≤ 3)
    (hR : ∀ S ∈ CN t G x y, R.card < 2 * (S ∩ R).card) : R.card = 3 := by
  classical
  by_contra h3
  apply hns
  have hle : R.card ≤ 2 := by omega
  rcases Nat.lt_or_ge R.card 1 with h0 | h1
  · have hR0 : R.card = 0 := by omega
    refine ⟨x, fun S hS => ?_⟩
    have := hR S hS
    rw [hR0] at this
    have h' : (S ∩ R).card ≤ R.card := card_le_card inter_subset_right
    omega
  · obtain ⟨w, hw⟩ := card_pos.1 (show 0 < R.card by omega)
    rcases Nat.lt_or_ge R.card 2 with h1' | h2
    · refine ⟨w, fun S hS => ?_⟩
      have := hR S hS
      obtain ⟨z, hz⟩ := card_pos.1 (show 0 < (S ∩ R).card by omega)
      rw [mem_inter] at hz
      have : z = w := card_le_one.1 (by omega) z hz.2 w hw
      exact this ▸ hz.1
    · refine ⟨w, fun S hS => ?_⟩
      have := hR S hS
      have hsub : S ∩ R = R := eq_of_subset_of_card_le inter_subset_right (by omega)
      have : w ∈ S ∩ R := by rw [hsub]; exact hw
      exact (mem_inter.1 this).1

lemma two_le_of_rt {S R : Finset (Fin n)} (hR3 : R.card = 3) (h : R.card < 2 * (S ∩ R).card) :
    2 ≤ (S ∩ R).card := by omega

/-- A non-star link with a root set of size three has at most `3 n^(t-3)` members. -/
lemma card_CN_le {t : ℕ} (ht : 4 ≤ t) {G : Finset (Finset (Fin n))} {x y : Fin n}
    {R : Finset (Fin n)} (hR3 : R.card = 3)
    (hR : ∀ S ∈ CN t G x y, R.card < 2 * (S ∩ R).card) :
    (CN t G x y).card ≤ 3 * n ^ (t - 3) := by
  classical
  have := card_le_cover (CN t G x y) (t - 1) 2 (R.powersetCard 2) id
    (fun T hT => (mem_powersetCard.1 hT).2) (by
      intro S hS
      refine ⟨(mem_CN.1 hS).1, ?_⟩
      obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq (two_le_of_rt hR3 (hR S hS))
      exact ⟨T, mem_powersetCard.2 ⟨hT.trans inter_subset_right, hTc⟩,
        hT.trans inter_subset_left⟩)
  rw [card_powersetCard, hR3] at this
  have h : t - 1 - 2 = t - 3 := by omega
  rw [h] at this
  simpa using this

/-! ## Heavy vertices -/

lemma mem_pair_of_rt {S R : Finset (Fin n)} {a b c : Fin n} (hR : R = {a, b, c})
    (h2 : 2 ≤ (S ∩ R).card) (hc : c ∉ S) : a ∈ S ∧ b ∈ S := by
  classical
  have hsub : S ∩ R ⊆ {a, b} := by
    intro z hz
    rw [mem_inter, hR] at hz
    simp only [mem_insert, mem_singleton] at hz ⊢
    rcases hz with ⟨hzS, rfl | rfl | rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hzS hc
  by_contra hab
  have : S ∩ R ⊆ ({a, b} : Finset (Fin n)).filter (fun z => z ∈ S) := by
    intro z hz
    exact mem_filter.2 ⟨hsub hz, (mem_inter.1 hz).1⟩
  have hc1 : (({a, b} : Finset (Fin n)).filter (fun z => z ∈ S)).card ≤ 1 := by
    rw [card_le_one]
    intro z hz w hw
    simp only [mem_filter, mem_insert, mem_singleton] at hz hw
    rcases hz with ⟨rfl | rfl, hz⟩ <;> rcases hw with ⟨rfl | rfl, hw⟩ <;> tauto
  have := card_le_card this
  omega

lemma build_mem {t : ℕ} {G : Finset (Finset (Fin n))} {x y w u v a b : Fin n}
    {P S1 S2 : Finset (Fin n)}
    (hS1 : S1 ∈ CN t G x y) (hS2 : S2 ∈ CN t G x y)
    (hw : ∀ S ∈ CN t G x y, w ∉ S ∧ insert w S ∈ G)
    (hS1eq : S1 = insert a (insert b (insert u P)))
    (hS2eq : S2 = insert a (insert b (insert v P)))
    (haT1 : a ∉ insert u P) (hbT1 : b ∉ insert u P)
    (haT2 : a ∉ insert v P) (hbT2 : b ∉ insert v P)
    (huv : u ≠ v) (huP : u ∉ P) (hvP : v ∉ P) :
    insert w (insert a (insert b P)) ∈ CN t G u v := by
  have hwS1 := (hw S1 hS1).1
  have hwS2 := (hw S2 hS2).1
  have hua : u ≠ a := fun h => haT1 (h ▸ mem_insert_self u P)
  have hub : u ≠ b := fun h => hbT1 (h ▸ mem_insert_self u P)
  have hva : v ≠ a := fun h => haT2 (h ▸ mem_insert_self v P)
  have hvb : v ≠ b := fun h => hbT2 (h ▸ mem_insert_self v P)
  have huw : u ≠ w := fun h => hwS1 (by rw [hS1eq, ← h]; simp)
  have hvw : v ≠ w := fun h => hwS2 (by rw [hS2eq, ← h]; simp)
  have hwab : w ∉ insert a (insert b P) := by
    intro h
    apply hwS1
    rw [hS1eq]
    exact insert_subset_insert a (insert_subset_insert b (subset_insert u P)) h
  have huab : u ∉ insert a (insert b P) := by
    simp only [mem_insert, not_or]; exact ⟨hua, hub, huP⟩
  rw [mem_CN]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [card_insert_of_notMem hwab]
    have h1 := (mem_CN.1 hS1).1
    rw [hS1eq, insert_comm b u, insert_comm a u, card_insert_of_notMem huab] at h1
    exact h1
  · simp only [mem_insert, not_or]; exact ⟨huw, hua, hub, huP⟩
  · simp only [mem_insert, not_or]; exact ⟨hvw, hva, hvb, hvP⟩
  · rw [insert_comm u w, insert_comm u a, insert_comm u b, ← hS1eq]
    exact (hw S1 hS1).2
  · rw [insert_comm v w, insert_comm v a, insert_comm v b, ← hS2eq]
    exact (hw S2 hS2).2

section Heavy

variable {t U B q : ℕ} {F G : Finset (Finset (Fin n))} (Rt : Fin n × Fin n → Finset (Fin n))

open scoped Classical in
/-- How many ordered pairs have `z` in their root set. -/
noncomputable def rootCount (z : Fin n) : ℕ :=
  (univ.offDiag.filter (fun p : Fin n × Fin n => z ∈ Rt p)).card

open scoped Classical in
noncomputable def Heavy (q : ℕ) : Finset (Fin n) :=
  univ.filter (fun z => q ^ 2 ≤ 4 * rootCount Rt z)

open scoped Classical in
lemma heavy_card (hRt3 : ∀ p, (Rt p).card ≤ 3) :
    (Heavy Rt q).card * q ^ 2 ≤ 12 * (n * n) := by
  have hsum : ∑ z, rootCount Rt z ≤ 3 * (n * n) := by
    have h1 : ∑ z, rootCount Rt z =
        ∑ p ∈ (univ.offDiag : Finset (Fin n × Fin n)), (Rt p).card := by
      unfold rootCount
      simp_rw [card_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      rw [← card_filter]
      congr 1
      ext z; simp
    rw [h1]
    calc _ ≤ ∑ _p ∈ (univ.offDiag : Finset (Fin n × Fin n)), 3 := sum_le_sum (fun p _ => hRt3 p)
      _ ≤ 3 * (n * n) := by
          rw [sum_const, smul_eq_mul, offDiag_card, card_univ, Fintype.card_fin, mul_comm]
          exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  calc (Heavy Rt q).card * q ^ 2 = ∑ _z ∈ Heavy Rt q, q ^ 2 := by simp
    _ ≤ ∑ z ∈ Heavy Rt q, 4 * rootCount Rt z := by
        apply sum_le_sum
        intro z hz
        exact (mem_filter.1 hz).2
    _ ≤ ∑ z, 4 * rootCount Rt z := sum_le_sum_of_subset (subset_univ _)
    _ = 4 * ∑ z, rootCount Rt z := by rw [mul_sum]
    _ ≤ 12 * (n * n) := by omega

/-- The first vertex of a non-star pair is not one of its roots. -/
lemma fst_notin_rt {x y : Fin n} (hns : ¬ Star (CN t G x y)) (hR3 : (Rt (x, y)).card = 3)
    (hR : ∀ S ∈ CN t G x y, (Rt (x, y)).card < 2 * (S ∩ Rt (x, y)).card) :
    x ∉ Rt (x, y) := by
  classical
  intro hx
  apply hns
  obtain ⟨w, hw⟩ : ((Rt (x, y)).erase x).Nonempty := by
    rw [← card_pos, card_erase_of_mem hx, hR3]; norm_num
  refine ⟨w, fun S hS => ?_⟩
  have h2 := hR S hS
  have hxS : x ∉ S := (mem_CN.1 hS).2.1
  have hsub : S ∩ Rt (x, y) ⊆ (Rt (x, y)).erase x := by
    intro z hz
    rw [mem_inter] at hz
    exact mem_erase.2 ⟨fun h => hxS (h ▸ hz.1), hz.2⟩
  have hc : ((Rt (x, y)).erase x).card = 2 := by rw [card_erase_of_mem hx, hR3]
  have heq : S ∩ Rt (x, y) = (Rt (x, y)).erase x :=
    eq_of_subset_of_card_le hsub (by rw [hc]; omega)
  have : w ∈ S ∩ Rt (x, y) := heq ▸ hw
  exact (mem_inter.1 this).1

variable (hRt3 : ∀ p, (Rt p).card ≤ 3)
  (hRt : ∀ p : Fin n × Fin n, p.1 ≠ p.2 → ∀ S ∈ CN t G p.1 p.2, (Rt p).card < 2 * (S ∩ Rt p).card)

include hRt3 hRt in
open scoped Classical in
/-- Two roots of a non-star pair: one of them is heavy. -/
lemma heavy_pair (ht : 4 ≤ t) (hn : 0 < n)
    (hP : F.card + U * NS t G ≤ G.card + B)
    (hmin : ∀ G' ⊆ G, F.card + U * NS t G' ≤ G'.card + B → G.card ≤ G'.card)
    (hUq : q * n ^ (t - 4) ≤ U) (hq2 : 2 * (t - 3) * n ≤ q ^ 2)
    {x y : Fin n} (hxy : x ≠ y) (hns : ¬ Star (CN t G x y))
    {a b : Fin n} (ha : a ∈ Rt (x, y)) (hb : b ∈ Rt (x, y)) (hab : a ≠ b) :
    a ∈ Heavy Rt q ∨ b ∈ Heavy Rt q := by
  set R := Rt (x, y) with hRdef
  have hRx : ∀ S ∈ CN t G x y, R.card < 2 * (S ∩ R).card := hRt (x, y) hxy
  have hR3 : R.card = 3 := rt_card_three hns (hRt3 _) hRx
  obtain ⟨c, hc⟩ : ((R.erase a).erase b).Nonempty := by
    rw [← card_pos, card_erase_of_mem (mem_erase.2 ⟨hab.symm, hb⟩), card_erase_of_mem ha, hR3]
    norm_num
  have hcb : c ≠ b := (mem_erase.1 hc).1
  have hca : c ≠ a := (mem_erase.1 (mem_of_mem_erase hc)).1
  have hcR : c ∈ R := mem_of_mem_erase (mem_of_mem_erase hc)
  have hReq : R = {a, b, c} := by
    symm
    apply eq_of_subset_of_card_le
    · intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with h | h | h
      · rw [h]; exact ha
      · rw [h]; exact hb
      · rw [h]; exact hcR
    · rw [hR3, card_three hab hca.symm hcb.symm]
  -- members missing `c`
  set Mc := (CN t G x y).filter (fun S => c ∉ S) with hMc
  have hMc_big : U ≤ Mc.card := miss_ge hP hmin hxy hns c
  have hMc_ab : ∀ S ∈ Mc, a ∈ S ∧ b ∈ S := by
    intro S hS
    rw [hMc, mem_filter] at hS
    exact mem_pair_of_rt hReq (two_le_of_rt hR3 (hRx S hS.1)) hS.2
  set 𝓡 := Mc.image (fun S => S \ {a, b}) with h𝓡
  have hab_sub : ∀ S ∈ Mc, ({a, b} : Finset (Fin n)) ⊆ S := by
    intro S hS z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    exacts [(hMc_ab S hS).1, (hMc_ab S hS).2]
  have h𝓡card : 𝓡.card = Mc.card := by
    apply card_image_of_injOn
    intro S hS S' hS' h
    have h' : S \ {a, b} = S' \ {a, b} := h
    rw [← sdiff_union_of_subset (hab_sub S hS), ← sdiff_union_of_subset (hab_sub S' hS'), h']
  have h𝓡m : ∀ T ∈ 𝓡, T.card = t - 3 := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := mem_image.1 hT
    rw [card_sdiff_of_subset (hab_sub S hS), card_pair hab,
      (mem_CN.1 (mem_filter.1 hS).1).1]
    omega
  -- unpacking members of `𝓡`
  have unpack : ∀ T ∈ 𝓡, ∃ S ∈ CN t G x y, S = insert a (insert b T) ∧ a ∉ T ∧ b ∉ T := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := mem_image.1 hT
    refine ⟨S, (mem_filter.1 hS).1, ?_, by simp, by simp⟩
    ext z
    simp only [mem_insert, mem_sdiff, mem_singleton]
    constructor
    · intro hz
      by_cases h1 : z = a
      · exact Or.inl h1
      · by_cases h2 : z = b
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨hz, by tauto⟩)
    · rintro (rfl | rfl | ⟨hz, -⟩)
      exacts [(hMc_ab S hS).1, (hMc_ab S hS).2, hz]
  -- many good pairs
  have hgood := good_pairs (m := t - 3) (q := q) hn (by omega) 𝓡 h𝓡m (by
    have : t - 3 - 1 = t - 4 := by omega
    rw [this, h𝓡card]; exact hUq.trans hMc_big)
  set good := univ.offDiag.filter (fun p : Fin n × Fin n => GoodPair 𝓡 p.1 p.2) with hgooddef
  -- a member of `CN(u, v)` built from `w ∈ {x, y}` and a link `P`
  have build : ∀ (w : Fin n) (u v : Fin n) (P : Finset (Fin n)),
      (∀ S ∈ CN t G x y, w ∉ S ∧ insert w S ∈ G) → u ≠ v → u ∉ P → v ∉ P →
      insert u P ∈ 𝓡 → insert v P ∈ 𝓡 →
      insert w (insert a (insert b P)) ∈ CN t G u v ∧ ∃ S1 ∈ CN t G x y, P ⊆ S1 := by
    intro w u v P hw huv huP hvP hu hv
    obtain ⟨S1, hS1, hS1eq, haT1, hbT1⟩ := unpack _ hu
    obtain ⟨S2, hS2, hS2eq, haT2, hbT2⟩ := unpack _ hv
    refine ⟨build_mem hS1 hS2 hw hS1eq hS2eq haT1 hbT1 haT2 hbT2 huv huP hvP, S1, hS1, ?_⟩
    rw [hS1eq]
    exact (subset_insert u P).trans ((subset_insert _ _).trans (subset_insert _ _))
  have hgood_sub : good ⊆ univ.offDiag.filter (fun p : Fin n × Fin n => a ∈ Rt p) ∪
      univ.offDiag.filter (fun p : Fin n × Fin n => b ∈ Rt p) := by
    intro p hp
    rw [hgooddef, mem_filter] at hp
    obtain ⟨hpO, P, Q, hPQ, huP, hvP, huQ, hvQ, h1, h2, h3, h4⟩ := hp
    have huv : p.1 ≠ p.2 := (mem_offDiag.1 hpO).2.2
    have hxw : ∀ S ∈ CN t G x y, x ∉ S ∧ insert x S ∈ G :=
      fun S hS => ⟨(mem_CN.1 hS).2.1, (mem_CN.1 hS).2.2.2.1⟩
    have hyw : ∀ S ∈ CN t G x y, y ∉ S ∧ insert y S ∈ G :=
      fun S hS => ⟨(mem_CN.1 hS).2.2.1, (mem_CN.1 hS).2.2.2.2⟩
    obtain ⟨hM1, S1, hS1, hP1⟩ := build x p.1 p.2 P hxw huv huP hvP h1 h2
    obtain ⟨hM2, S3, hS3, hQ1⟩ := build y p.1 p.2 Q hyw huv huQ hvQ h3 h4
    have hyS1 : y ∉ S1 := (mem_CN.1 hS1).2.2.1
    have hxS3 : x ∉ S3 := (mem_CN.1 hS3).2.1
    have hr1 := hRt p huv _ hM1
    have hr2 := hRt p huv _ hM2
    obtain ⟨z, hz⟩ := inter_nonempty_of_rt hr1 hr2
    obtain ⟨hz1, hz2, hzR⟩ := hz
    have hzab : z = a ∨ z = b := by
      rw [mem_insert, mem_insert, mem_insert] at hz1 hz2
      rcases hz1 with rfl | rfl | rfl | hzP
      · rcases hz2 with h | h | h | hzQ
        · exact absurd h hxy
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd (hQ1 hzQ) hxS3
      · exact Or.inl rfl
      · exact Or.inr rfl
      · rcases hz2 with rfl | h | h | hzQ
        · exact absurd (hP1 hzP) hyS1
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd hzQ (disjoint_left.1 hPQ hzP)
    rw [mem_union, mem_filter, mem_filter]
    rcases hzab with rfl | rfl
    · exact Or.inl ⟨hpO, hzR⟩
    · exact Or.inr ⟨hpO, hzR⟩
  have hcount : good.card ≤ rootCount Rt a + rootCount Rt b :=
    (card_le_card hgood_sub).trans (card_union_le _ _)
  have h2 : 2 * (t - 3) * n = 2 * ((t - 3) * n) := by ring
  unfold Heavy
  simp only [mem_filter, mem_univ, true_and]
  omega

end Heavy

/-! ## Few non-star pairs -/

open scoped Classical in
/-- Every vertex lies in at most `J |H|²` non-star pairs of the minimal subfamily. -/
lemma few_nonstar {t U B q J : ℕ} {F G : Finset (Finset (Fin n))}
    (Rt : Fin n × Fin n → Finset (Fin n)) (hRt3 : ∀ p, (Rt p).card ≤ 3)
    (hRt : ∀ p : Fin n × Fin n, p.1 ≠ p.2 → ∀ S ∈ CN t G p.1 p.2, (Rt p).card < 2 * (S ∩ Rt p).card)
    (ht : 4 ≤ t) (hn : 0 < n) (hGt : ∀ E ∈ G, E.card = t)
    (hP : F.card + U * NS t G ≤ G.card + B)
    (hmin : ∀ G' ⊆ G, F.card + U * NS t G' ≤ G'.card + B → G.card ≤ G'.card)
    (hUq : q * n ^ (t - 4) ≤ U) (hq2 : 2 * (t - 3) * n ≤ q ^ 2)
    (hJ : n ^ (t - 3) < U * (J + 1)) (x : Fin n) :
    (univ.filter (fun y => x ≠ y ∧ ¬ Star (CN t G x y))).card ≤
      (Heavy Rt q ×ˢ Heavy Rt q).card * J := by
  set H := Heavy Rt q
  set Y := univ.filter (fun y => x ≠ y ∧ ¬ Star (CN t G x y)) with hY
  have hpair : ∀ y ∈ Y, ∃ ab ∈ H ×ˢ H, ab.1 ≠ ab.2 ∧ ab.1 ∈ Rt (x, y) ∧ ab.2 ∈ Rt (x, y) := by
    intro y hy
    simp only [hY, mem_filter, mem_univ, true_and] at hy
    have hR3 := rt_card_three hy.2 (hRt3 _) (hRt (x, y) hy.1)
    obtain ⟨a, b, c, hab, hac, hbc, hR⟩ := card_eq_three.1 hR3
    have ha : a ∈ Rt (x, y) := by rw [hR]; simp
    have hb : b ∈ Rt (x, y) := by rw [hR]; simp
    have hc : c ∈ Rt (x, y) := by rw [hR]; simp
    have hp := fun {a b} ha hb hab =>
      heavy_pair (F := F) (U := U) (B := B) Rt hRt3 hRt ht hn hP hmin hUq hq2 hy.1 hy.2
        (a := a) (b := b) ha hb hab
    by_cases haH : a ∈ H
    · rcases hp hb hc hbc with h | h
      · exact ⟨(a, b), mem_product.2 ⟨haH, h⟩, hab, ha, hb⟩
      · exact ⟨(a, c), mem_product.2 ⟨haH, h⟩, hac, ha, hc⟩
    · have hbH := (hp ha hb hab).resolve_left haH
      have hcH := (hp ha hc hac).resolve_left haH
      exact ⟨(b, c), mem_product.2 ⟨hbH, hcH⟩, hbc, hb, hc⟩
  choose! f hf using hpair
  by_contra hlt
  push_neg at hlt
  obtain ⟨ab, hab, hfib⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (fun y hy => (hf y hy).1) hlt
  set Yab := Y.filter (fun y => f y = ab) with hYab
  obtain ⟨y0, hy0⟩ : Yab.Nonempty := by rw [← card_pos]; omega
  have hy0Y : y0 ∈ Y := (mem_filter.1 hy0).1
  have hfy0 : f y0 = ab := (mem_filter.1 hy0).2
  obtain ⟨-, habne, ha0, hb0⟩ := hf y0 hy0Y
  rw [hfy0] at habne ha0 hb0
  set a := ab.1
  set b := ab.2
  have hy0' : x ≠ y0 ∧ ¬ Star (CN t G x y0) := by
    simpa [hY] using hy0Y
  have hR3y0 := rt_card_three hy0'.2 (hRt3 _) (hRt (x, y0) hy0'.1)
  have hxR := fst_notin_rt Rt hy0'.2 hR3y0 (hRt (x, y0) hy0'.1)
  have hxa : x ≠ a := fun h => hxR (h ▸ ha0)
  have hxb : x ≠ b := fun h => hxR (h ▸ hb0)
  set G' := G.filter (fun E => ¬ ({x, a, b} ⊆ E)) with hG'
  have hG'G : G' ⊆ G := filter_subset _ _
  have hcost : G.card ≤ G'.card + n ^ (t - 3) := by
    have h1 : G.card ≤ G'.card + (G.filter (fun E => {x, a, b} ⊆ E)).card := by
      calc G.card ≤ (G' ∪ G.filter (fun E => {x, a, b} ⊆ E)).card := by
            apply card_le_card
            intro E hE
            by_cases h : {x, a, b} ⊆ E
            · exact mem_union_right _ (mem_filter.2 ⟨hE, h⟩)
            · exact mem_union_left _ (mem_filter.2 ⟨hE, h⟩)
        _ ≤ _ := card_union_le _ _
    have h2 : (G.filter (fun E => {x, a, b} ⊆ E)).card ≤ n ^ (t - 3) := by
      have := card_supersets_le t ({x, a, b} : Finset (Fin n))
      rw [card_three hxa hxb habne] at this
      refine le_trans (card_le_card ?_) this
      intro E hE
      rw [mem_filter] at hE ⊢
      exact ⟨mem_powersetCard.2 ⟨subset_univ _, hGt E hE.1⟩, hE.2⟩
    omega
  set Q := Yab.image (fun y => (x, y)) with hQ
  have hQcard : Q.card = Yab.card := card_image_of_injective _ (fun y y' h => by
    simpa using h)
  have hNS : NS t G' + Q.card ≤ NS t G := by
    apply NS_add_le hG'G
    intro p hp
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hp
    have hyY : y ∈ Y := (mem_filter.1 hy).1
    have hfy : f y = ab := (mem_filter.1 hy).2
    have hy' : x ≠ y ∧ ¬ Star (CN t G x y) := by simpa [hY] using hyY
    refine ⟨hy'.1, hy'.2, ?_⟩
    obtain ⟨-, habne', ha', hb'⟩ := hf y hyY
    rw [hfy] at ha' hb'
    have hRx := hRt (x, y) hy'.1
    have hR3 := rt_card_three hy'.2 (hRt3 _) hRx
    obtain ⟨c, hc⟩ : (((Rt (x, y)).erase a).erase b).Nonempty := by
      rw [← card_pos, card_erase_of_mem (mem_erase.2 ⟨habne.symm, hb'⟩),
        card_erase_of_mem ha', hR3]
      norm_num
    have hcb : c ≠ b := (mem_erase.1 hc).1
    have hca : c ≠ a := (mem_erase.1 (mem_of_mem_erase hc)).1
    have hcR : c ∈ Rt (x, y) := mem_of_mem_erase (mem_of_mem_erase hc)
    have hReq : Rt (x, y) = {a, b, c} := by
      symm
      apply eq_of_subset_of_card_le
      · intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with h | h | h
        · rw [h]; exact ha'
        · rw [h]; exact hb'
        · rw [h]; exact hcR
      · rw [hR3, card_three habne hca.symm hcb.symm]
    refine ⟨c, fun S hS => ?_⟩
    have hSG : S ∈ CN t G x y := CN_mono hG'G x y hS
    by_contra hcS
    obtain ⟨haS, hbS⟩ := mem_pair_of_rt hReq (two_le_of_rt hR3 (hRx S hSG)) hcS
    have hxS' : insert x S ∈ G' := (mem_CN.1 hS).2.2.2.1
    apply (mem_filter.1 hxS').2
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem haS
    · exact mem_insert_of_mem hbS
  apply no_cheap_improvement hP hmin hG'G (j := Q.card) (by omega) hNS
  have : U * (J + 1) ≤ U * Q.card := Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## Starification for a fixed order -/

open scoped Classical in
lemma starify {t U B q J h0 : ℕ} (ht : 4 ≤ t) (hn : 0 < n)
    (F : Finset (Finset (Fin n))) (hFt : F.IsUniform t) (hF : ¬ F.HasRepeatedDisjointUnion)
    (hB : n * n * U ≤ B)
    (hU3 : (t - 1) ^ 3 * n ^ (t - 4) < U) (hUq : q * n ^ (t - 4) ≤ U)
    (hq2 : 2 * (t - 3) * n ≤ q ^ 2) (hJ : n ^ (t - 3) < U * (J + 1))
    (hH : ∀ h : ℕ, h * q ^ 2 ≤ 12 * (n * n) → h ≤ h0) :
    ∃ G ⊆ F, (∀ x y : Fin n, x ≠ y → Star (CN t G x y)) ∧
      F.card ≤ G.card + B + n * (h0 * h0 * J) * (3 * n ^ (t - 3)) := by
  set S := F.powerset.filter (fun G => F.card + U * NS t G ≤ G.card + B) with hS
  have hFS : F ∈ S := by
    rw [hS, mem_filter]
    refine ⟨mem_powerset_self F, ?_⟩
    have := Nat.mul_le_mul_left U (NS_le_sq t F)
    have : U * (n * n) = n * n * U := by ring
    omega
  obtain ⟨G, hGS, hGmin⟩ := exists_min_image S card ⟨F, hFS⟩
  rw [hS, mem_filter, mem_powerset] at hGS
  obtain ⟨hGF, hP⟩ := hGS
  have hmin : ∀ G' ⊆ G, F.card + U * NS t G' ≤ G'.card + B → G.card ≤ G'.card := by
    intro G' hG' hP'
    exact hGmin G' (by rw [hS, mem_filter, mem_powerset]; exact ⟨hG'.trans hGF, hP'⟩)
  have hGt : ∀ E ∈ G, E.card = t := fun E hE => hFt E (hGF hE)
  choose Rt hRt3 hRt using rt_exists (t := t) ht hn hF hGF hP hmin hU3
  have hRt' : ∀ p : Fin n × Fin n, p.1 ≠ p.2 → ∀ S ∈ CN t G p.1 p.2,
      (Rt p).card < 2 * (S ∩ Rt p).card := hRt
  have hHc : (Heavy Rt q).card ≤ h0 := hH _ (heavy_card Rt hRt3)
  have hfew : ∀ x : Fin n, (univ.filter (fun y => x ≠ y ∧ ¬ Star (CN t G x y))).card ≤
      h0 * h0 * J := by
    intro x
    refine (few_nonstar Rt hRt3 hRt' ht hn hGt hP hmin hUq hq2 hJ x).trans ?_
    rw [card_product]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hHc hHc)
  set NSs := univ.offDiag.filter (fun p : Fin n × Fin n => ¬ Star (CN t G p.1 p.2)) with hNSs
  have hNSs_card : NSs.card ≤ n * (h0 * h0 * J) := by
    rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun p _ => mem_univ _)]
    calc ∑ x ∈ univ, (NSs.filter (fun p => p.1 = x)).card
        ≤ ∑ _x ∈ (univ : Finset (Fin n)), h0 * h0 * J := by
          apply sum_le_sum
          intro x _
          refine le_trans ?_ (hfew x)
          apply card_le_card_of_injOn Prod.snd
          · intro p hp
            simp only [coe_filter, hNSs, mem_filter, mem_offDiag, mem_univ, true_and,
              Set.mem_setOf_eq] at hp ⊢
            obtain ⟨⟨hne, hns⟩, rfl⟩ := hp
            exact ⟨hne, hns⟩
          · intro p hp p' hp' h
            simp only [coe_filter, hNSs, mem_filter, Set.mem_setOf_eq] at hp hp'
            exact Prod.ext (hp.2.trans hp'.2.symm) h
      _ = n * (h0 * h0 * J) := by simp
  set Del := NSs.biUnion (fun p => (CN t G p.1 p.2).image (insert p.1)) with hDel
  have hDel_card : Del.card ≤ n * (h0 * h0 * J) * (3 * n ^ (t - 3)) := by
    calc Del.card ≤ ∑ p ∈ NSs, ((CN t G p.1 p.2).image (insert p.1)).card := card_biUnion_le
      _ ≤ ∑ _p ∈ NSs, 3 * n ^ (t - 3) := by
          apply sum_le_sum
          intro p hp
          simp only [hNSs, mem_filter, mem_offDiag, mem_univ, true_and] at hp
          refine card_image_le.trans ?_
          exact card_CN_le ht (rt_card_three hp.2 (hRt3 p) (hRt p hp.1)) (hRt p hp.1)
      _ = NSs.card * (3 * n ^ (t - 3)) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hNSs_card
  refine ⟨G \ Del, sdiff_subset.trans hGF, ?_, ?_⟩
  · intro x y hxy
    by_cases hs : Star (CN t G x y)
    · exact star_mono (CN_mono sdiff_subset x y) hs
    · refine ⟨⟨0, hn⟩, fun S hS => ?_⟩
      exfalso
      have hSG : S ∈ CN t G x y := CN_mono sdiff_subset x y hS
      have h1 : insert x S ∈ G \ Del := (mem_CN.1 hS).2.2.2.1
      apply (mem_sdiff.1 h1).2
      rw [hDel, mem_biUnion]
      refine ⟨(x, y), ?_, mem_image.2 ⟨S, hSG, rfl⟩⟩
      simp only [hNSs, mem_filter, mem_offDiag, mem_univ, true_and]
      exact ⟨hxy, hs⟩
  · have h1 : G.card ≤ (G \ Del).card + Del.card := by
      have := card_sdiff_add_card_inter G Del
      have h2 : (G ∩ Del).card ≤ Del.card := card_le_card inter_subset_right
      omega
    omega

/-! ## The binomial lower bound -/

lemma power_le_binomial {n k : ℕ} (hn : 0 < n) (hlarge : 2 * k ≤ n) :
    n ^ k ≤ 2 ^ k * k.factorial * (n - 1).choose k := by
  have hbase : n ≤ 2 * (n - k) := by omega
  have hpow : (n - k) ^ k ≤ (n - 1).descFactorial k := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using
      (n - 1).pow_sub_le_descFactorial k
  calc
    n ^ k ≤ (2 * (n - k)) ^ k := Nat.pow_le_pow_left hbase k
    _ = 2 ^ k * (n - k) ^ k := mul_pow _ _ _
    _ ≤ 2 ^ k * (n - 1).descFactorial k := Nat.mul_le_mul_left _ hpow
    _ = _ := by rw [Nat.descFactorial_eq_factorial_mul_choose, mul_assoc]

end OMA_E643LS

open OMA_E643LS in
theorem OMA.solution : OMA.R_Erdos643_erdos_643_parts_ii_R1_H2_R1_H1_R1.H1 := by
  intro t ht ε hε
  set C : ℕ := 2 ^ (t - 1) * (t - 1).factorial with hC
  have hCpos : 0 < C := by positivity
  set L : ℕ := ⌈2 * (C : ℝ) / ε⌉₊ + 1 with hL
  have hLpos : 0 < L := by omega
  have hLε : 2 * (C : ℝ) ≤ ε * L := by
    have h1 : 2 * (C : ℝ) / ε ≤ ⌈2 * (C : ℝ) / ε⌉₊ := Nat.le_ceil _
    have h2 : (⌈2 * (C : ℝ) / ε⌉₊ : ℝ) ≤ L := by rw [hL]; push_cast; linarith
    rw [div_le_iff₀ hε] at h1
    nlinarith
  set h0 : ℕ := 48 * L ^ 2 with hh0
  set J : ℕ := 2 * L with hJdef
  set K : ℕ := h0 * h0 * J with hK
  set Q0 : ℕ := (t - 1) ^ 3 + 4 * L * (t - 3) + 1 with hQ0
  set N1 : ℕ := ⌈6 * (K : ℝ) * C / ε⌉₊ with hN1
  rw [Filter.eventually_atTop]
  refine ⟨L * Q0 + 2 * (t - 1) + 2 * L + N1 + 1, fun n hn => ?_⟩
  intro F hFt hF hFs
  have hn0 : 0 < n := by omega
  set q := n / L with hq
  have hqQ0 : Q0 ≤ q := by rw [hq, Nat.le_div_iff_mul_le hLpos]; nlinarith
  have hq1 : 1 ≤ q := by omega
  have hnq : n ≤ 2 * L * q := by
    have h1 := Nat.div_add_mod n L
    have h2 := Nat.mod_lt n hLpos
    rw [← hq] at h1
    nlinarith
  have hnpow : 0 < n ^ (t - 4) := pow_pos hn0 _
  set U := q * n ^ (t - 4) with hU
  set B := n * n * U with hB
  have hU3 : (t - 1) ^ 3 * n ^ (t - 4) < U := Nat.mul_lt_mul_of_pos_right (by omega) hnpow
  have hq2 : 2 * (t - 3) * n ≤ q ^ 2 := by
    calc 2 * (t - 3) * n ≤ 2 * (t - 3) * (2 * L * q) := Nat.mul_le_mul_left _ hnq
      _ = (4 * L * (t - 3)) * q := by ring
      _ ≤ q * q := Nat.mul_le_mul_right _ (by omega)
      _ = q ^ 2 := by ring
  have hJ : n ^ (t - 3) < U * (J + 1) := by
    have he : n ^ (t - 3) = n * n ^ (t - 4) := by
      rw [← pow_succ']; congr 1; omega
    rw [he, hU]
    have : n < q * (J + 1) := by rw [hJdef]; nlinarith
    calc n * n ^ (t - 4) < q * (J + 1) * n ^ (t - 4) := Nat.mul_lt_mul_of_pos_right this hnpow
      _ = q * n ^ (t - 4) * (J + 1) := by ring
  have hH : ∀ h : ℕ, h * q ^ 2 ≤ 12 * (n * n) → h ≤ h0 := by
    intro h hh
    have h1 : 12 * (n * n) ≤ h0 * q ^ 2 := by
      calc 12 * (n * n) ≤ 12 * ((2 * L * q) * (2 * L * q)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul hnq hnq)
        _ = h0 * q ^ 2 := by rw [hh0]; ring
    exact Nat.le_of_mul_le_mul_right (hh.trans h1) (by positivity)
  obtain ⟨G, hGF, hstar, hcard⟩ := starify (J := J) (h0 := h0) ht hn0 F hFt hF le_rfl
    hU3 le_rfl hq2 hJ hH
  refine ⟨G, hGF, fun E hE => hFt E (hGF hE), fun h => hF (hasRDU_mono hGF h), ?_, ?_⟩
  · -- the size bound
    clear_value C L h0 J K Q0 N1 q U B
    set s := (n - 1).choose (t - 1) with hs
    have hbin : n ^ (t - 1) ≤ C * s := by
      have := power_le_binomial (k := t - 1) hn0 (by omega)
      rw [hC]; linarith
    have hLB : L * B ≤ C * s := by
      refine le_trans ?_ hbin
      have hLq : L * q ≤ n := by rw [hq]; exact Nat.mul_div_le n L
      have he : n ^ (t - 1) = n * n * n * n ^ (t - 4) := by
        rw [show t - 1 = (t - 4) + 3 by omega, pow_add]; ring
      rw [he, hB, hU]
      calc L * (n * n * (q * n ^ (t - 4))) = n * n * (L * q) * n ^ (t - 4) := by ring
        _ ≤ n * n * n * n ^ (t - 4) := by gcongr
    set X := n * K * (3 * n ^ (t - 3)) with hX
    have hnX : n * X ≤ 3 * K * (C * s) := by
      refine le_trans ?_ (Nat.mul_le_mul_left (3 * K) hbin)
      have he : n ^ (t - 1) = n * n * n ^ (t - 3) := by
        rw [show t - 1 = (t - 3) + 2 by omega, pow_add]; ring
      rw [he, hX]; ring_nf; exact le_refl _
    clear_value s X
    have hnN1 : 6 * (K : ℝ) * C / ε ≤ n := by
      have := Nat.le_ceil (6 * (K : ℝ) * C / ε)
      have h2 : (N1 : ℝ) ≤ n := (Nat.cast_le (α := ℝ)).2 (show N1 ≤ n by omega)
      rw [← hN1] at this; linarith only [this, h2]
    have hεn : 6 * (K : ℝ) * C ≤ ε * n := by
      rw [mul_comm ε]; exact (div_le_iff₀ hε).1 hnN1
    have hcardR : (F.card : ℝ) ≤ G.card + B + X := by
      have h := (Nat.cast_le (α := ℝ)).2 (show F.card ≤ G.card + B + X by
        rw [hX, hB, hK]; exact hcard)
      rwa [Nat.cast_add, Nat.cast_add] at h
    have hFsR : (s : ℝ) ≤ F.card := (Nat.cast_le (α := ℝ)).2 hFs
    have hLBR : (L : ℝ) * B ≤ C * s := by
      have h := (Nat.cast_le (α := ℝ)).2 hLB
      rwa [Nat.cast_mul, Nat.cast_mul] at h
    have hnXR : (n : ℝ) * X ≤ 3 * K * (C * s) := by
      have h := (Nat.cast_le (α := ℝ)).2 hnX
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul] at h
      have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
      rw [h3] at h
      exact h
    have hs0 : (0 : ℝ) ≤ s := by positivity
    have hBR : 2 * (B : ℝ) ≤ ε * s := by
      have hL0 : (0 : ℝ) < L := Nat.cast_pos.2 hLpos
      have : (L : ℝ) * (2 * B) ≤ L * (ε * s) := by
        calc (L : ℝ) * (2 * B) = 2 * (L * B) := by ring
          _ ≤ 2 * (C * s) := by linarith only [hLBR]
          _ = (2 * C) * s := by ring
          _ ≤ (ε * L) * s := mul_le_mul_of_nonneg_right hLε hs0
          _ = L * (ε * s) := by ring
      exact le_of_mul_le_mul_left this hL0
    have hXR : 2 * (X : ℝ) ≤ ε * s := by
      have hn0' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
      have : (n : ℝ) * (2 * X) ≤ n * (ε * s) := by
        calc (n : ℝ) * (2 * X) = 2 * (n * X) := by ring
          _ ≤ 2 * (3 * K * (C * s)) := by linarith only [hnXR]
          _ = (6 * K * C) * s := by ring
          _ ≤ (ε * n) * s := mul_le_mul_of_nonneg_right hεn hs0
          _ = n * (ε * s) := by ring
      exact le_of_mul_le_mul_left this hn0'
    push_cast
    linarith only [hcardR, hFsR, hBR, hXR]
  · intro x y hxy
    obtain ⟨v, hv⟩ := hstar x y hxy
    refine ⟨v, fun S hS hxS hyS hxG hyG => hv S ?_⟩
    rw [mem_CN]
    exact ⟨hS, hxS, hyS, hxG, hyG⟩
