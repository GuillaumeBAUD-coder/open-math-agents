import OMAReductions.R_Erdos1057_erdos_1057_variants_agp_lower_bound_R1

-- Step Erdos1057.erdos_1057.variants.agp_lower_bound.R1.H2: hypothesis H2 of reduction Erdos1057.erdos_1057.variants.agp_lower_bound.R1

/-!
The counting lemma of Alford, Granville and Pomerance. Every `t`-subset `S` of `P` contains a
subset `I` with product `≡ 1` and `|S \ I| ≤ n` (take `I` of maximal size: a larger remainder
would contain a further nonempty subset with product `≡ 1`). So the `t`-subsets are covered by the
fibres `{S ⊇ I}` over such `I`, and a fibre has `choose (|P| - |I|) (t - |I|) ≤ choose |P| n`
elements.
-/

open Finset

namespace OMA

theorem exists_large (P : Finset ℕ) (M n : ℕ)
    (h : ∀ S ⊆ P, n < S.card → ∃ I ⊆ S, I.Nonempty ∧ (∏ p ∈ I, p) ≡ 1 [MOD M])
    (S : Finset ℕ) (hS : S ⊆ P) :
    ∃ I ⊆ S, (∏ p ∈ I, p) ≡ 1 [MOD M] ∧ S.card ≤ I.card + n := by
  classical
  have hne : (S.powerset.filter (fun I => (∏ p ∈ I, p) ≡ 1 [MOD M])).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset S, by simp [Nat.ModEq]⟩⟩
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  obtain ⟨hIS, hI1⟩ := Finset.mem_filter.1 hI
  rw [Finset.mem_powerset] at hIS
  refine ⟨I, hIS, hI1, ?_⟩
  by_contra hcon
  have hbig : n < (S \ I).card := by
    have := Finset.card_sdiff_add_card_eq_card hIS
    omega
  obtain ⟨J, hJ, hJne, hJ1⟩ := h (S \ I) (Finset.sdiff_subset.trans hS) hbig
  have hdisj : Disjoint I J := by
    rw [Finset.disjoint_left]
    intro x hxI hxJ
    exact (Finset.mem_sdiff.1 (hJ hxJ)).2 hxI
  have hIJ : I ∪ J ∈ S.powerset.filter (fun I => (∏ p ∈ I, p) ≡ 1 [MOD M]) := by
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2
      (Finset.union_subset hIS (hJ.trans Finset.sdiff_subset)), ?_⟩
    rw [Finset.prod_union hdisj]
    simpa using hI1.mul hJ1
  have h1 := hmax _ hIJ
  rw [Finset.card_union_of_disjoint hdisj] at h1
  have h2 := Finset.card_pos.2 hJne
  omega

theorem choose_bound (L i t n : ℕ) (hit : i ≤ t) (htL : t ≤ L) (htin : t ≤ i + n) (hnt : n ≤ t) :
    (L - i).choose (t - i) ≤ L.choose n := by
  have e1 : (L - i).choose (t - i) = (L - i).choose (L - t) := by
    have h := Nat.choose_symm (show t - i ≤ L - i by omega)
    rw [← h]
    congr 1
    omega
  have e2 : (L - i).choose (L - t) ≤ ((L - t) + n).choose (L - t) :=
    Nat.choose_le_choose _ (by omega)
  have e3 : ((L - t) + n).choose (L - t) = ((L - t) + n).choose n := Nat.choose_symm_add
  have e4 : ((L - t) + n).choose n ≤ L.choose n := Nat.choose_le_choose _ (by omega)
  omega

theorem count (P : Finset ℕ) (M n t : ℕ) (hnt : n ≤ t) (htP : t ≤ P.card)
    (h : ∀ S ⊆ P, n < S.card → ∃ I ⊆ S, I.Nonempty ∧ (∏ p ∈ I, p) ≡ 1 [MOD M])
    (F : Finset (Finset ℕ))
    (hF : ∀ I ⊆ P, t - n ≤ I.card → I.card ≤ t → (∏ p ∈ I, p) ≡ 1 [MOD M] → I ∈ F) :
    P.card.choose t ≤ F.card * P.card.choose n := by
  classical
  have hcover : P.powersetCard t ⊆
      F.biUnion (fun I => (P.powersetCard t).filter (fun S => I ⊆ S ∧ t ≤ I.card + n)) := by
    intro S hS
    obtain ⟨hSP, hSc⟩ := Finset.mem_powersetCard.1 hS
    obtain ⟨I, hIS, hI1, hcard⟩ := OMA.exists_large P M n h S hSP
    have hIc : I.card ≤ t := hSc ▸ Finset.card_le_card hIS
    have hIF : I ∈ F := hF I (hIS.trans hSP) (by omega) hIc hI1
    exact Finset.mem_biUnion.2 ⟨I, hIF, Finset.mem_filter.2 ⟨hS, hIS, by omega⟩⟩
  have hfibre : ∀ I ∈ F,
      ((P.powersetCard t).filter (fun S => I ⊆ S ∧ t ≤ I.card + n)).card ≤ P.card.choose n := by
    intro I _
    rcases ((P.powersetCard t).filter
      (fun S => I ⊆ S ∧ t ≤ I.card + n)).eq_empty_or_nonempty with he | ⟨S0, hS0⟩
    · rw [he]
      simp
    · obtain ⟨hS0m, hIS0, htin⟩ := Finset.mem_filter.1 hS0
      obtain ⟨hS0P, hS0c⟩ := Finset.mem_powersetCard.1 hS0m
      have hIP : I ⊆ P := hIS0.trans hS0P
      have hIt : I.card ≤ t := hS0c ▸ Finset.card_le_card hIS0
      have hinj : ((P.powersetCard t).filter (fun S => I ⊆ S ∧ t ≤ I.card + n)).card ≤
          ((P \ I).powersetCard (t - I.card)).card := by
        apply Finset.card_le_card_of_injOn (fun S => S \ I)
        · intro S hS
          obtain ⟨hSm, hIS, _⟩ := Finset.mem_filter.1 hS
          obtain ⟨hSP, hSc⟩ := Finset.mem_powersetCard.1 hSm
          refine Finset.mem_powersetCard.2 ⟨Finset.sdiff_subset_sdiff hSP (le_refl I), ?_⟩
          show (S \ I).card = t - I.card
          have := Finset.card_sdiff_add_card_eq_card hIS
          omega
        · intro S1 hS1 S2 hS2 heq
          have hI1 : I ⊆ S1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hS1)).2.1
          have hI2 : I ⊆ S2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hS2)).2.1
          have heq2 : S1 \ I = S2 \ I := heq
          rw [← Finset.sdiff_union_of_subset hI1, ← Finset.sdiff_union_of_subset hI2, heq2]
      rw [Finset.card_powersetCard] at hinj
      have hPI : (P \ I).card = P.card - I.card := by
        have := Finset.card_sdiff_add_card_eq_card hIP
        omega
      rw [hPI] at hinj
      exact hinj.trans (OMA.choose_bound P.card I.card t n hIt htP htin hnt)
  calc P.card.choose t = (P.powersetCard t).card := (Finset.card_powersetCard t P).symm
    _ ≤ (F.biUnion (fun I =>
          (P.powersetCard t).filter (fun S => I ⊆ S ∧ t ≤ I.card + n))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ I ∈ F, ((P.powersetCard t).filter (fun S => I ⊆ S ∧ t ≤ I.card + n)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _I ∈ F, P.card.choose n := Finset.sum_le_sum hfibre
    _ = F.card * P.card.choose n := by rw [Finset.sum_const, smul_eq_mul]

end OMA

theorem OMA.solution : OMA.R_Erdos1057_erdos_1057_variants_agp_lower_bound_R1.H2 := by
  unfold OMA.R_Erdos1057_erdos_1057_variants_agp_lower_bound_R1.H2
  intro P M n t hnt htP h
  exact OMA.count P M n t hnt htP h _
    (fun I hIP h1 h2 h3 => Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hIP, h1, h2, h3⟩)
