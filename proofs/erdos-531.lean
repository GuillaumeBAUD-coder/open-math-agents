import OMAStatements.S_erdos_531

-- Erdős Problem 531: Existence and threshold characterization of two-colour Folkman numbers
-- Credit: @EmadY

private def folkSt (b : Stream' ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => folkSt b i + (∑ j ∈ Finset.range (folkSt b i), b.get j) + 1

private lemma fs_pos : ∀ {a : Stream' ℕ} {m : ℕ}, m ∈ Hindman.FS a → (∀ n, 1 ≤ a.get n) → 1 ≤ m := by
  intro a m hm
  induction hm with
  | head' b => intro hb; exact hb 0
  | tail' b m _ ih => intro hb; exact ih fun n => hb (n + 1)
  | cons' b m _ ih =>
    intro hb
    have h0 := hb 0
    have h1 := ih fun n => hb (n + 1)
    omega

private lemma folk_exists_forces (k : ℕ) :
    ∃ N : ℕ, OMA.S_erdos_531.ForcesMonoSums k N := by
  by_contra hno
  have hbad : ∀ N, ∃ red : Finset ℕ, ∀ A ∈ (Finset.Icc 1 N).powersetCard k,
      ¬ (OMA.S_erdos_531.subsetSums A ⊆ red ∨
        OMA.S_erdos_531.subsetSums A ⊆ Finset.Icc 1 N \ red) := fun N => by
    by_contra h
    exact hno ⟨N, fun red _ => Classical.byContradiction fun hA =>
      h ⟨red, fun A hAm hm => hA ⟨A, hAm, hm⟩⟩⟩
  let red : ℕ → Finset ℕ := fun N => (hbad N).choose
  have havoid : ∀ N, ∀ A ∈ (Finset.Icc 1 N).powersetCard k,
      ¬ (OMA.S_erdos_531.subsetSums A ⊆ red N ∨
        OMA.S_erdos_531.subsetSums A ⊆ Finset.Icc 1 N \ red N) :=
    fun N => (hbad N).choose_spec
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  let C0 : Set ℕ := {m | 1 ≤ m ∧ {N | m ∈ red N} ∈ (U : Filter ℕ)}
  let C1 : Set ℕ := {m | 1 ≤ m ∧ {N | m ∉ red N} ∈ (U : Filter ℕ)}
  let ones : Stream' ℕ := fun _ => 1
  have hcov : Hindman.FS ones ⊆ ⋃₀ ({C0, C1} : Set (Set ℕ)) := fun m hm => by
    have hm1 : 1 ≤ m := fs_pos hm fun _ => le_rfl
    rcases U.em (fun N => m ∈ red N) with hU | hU
    · exact Set.mem_sUnion.mpr ⟨C0, Set.mem_insert _ _, hm1, hU⟩
    · exact Set.mem_sUnion.mpr ⟨C1, Set.mem_insert_of_mem _ (Set.mem_singleton _), hm1, hU⟩
  obtain ⟨C, hCS, b, hb⟩ := Hindman.FS_partition_regular ones {C0, C1} (by simp) hcov
  have hb1 : ∀ j, 1 ≤ b.get j := fun j => by
    rcases Set.mem_insert_iff.mp hCS with rfl | hC1
    · exact (hb (Hindman.FS.singleton b j)).1
    · rw [Set.mem_singleton_iff.mp hC1] at hb
      exact (hb (Hindman.FS.singleton b j)).1
  let s := folkSt b
  let I : ℕ → Finset ℕ := fun i => Finset.Ico (s i) (s (i + 1))
  let y : ℕ → ℕ := fun i => ∑ j ∈ I i, b.get j
  have hs_lt : ∀ i, s i < s (i + 1) := fun i => by
    change folkSt b i < folkSt b i + (∑ j ∈ Finset.range (folkSt b i), b.get j) + 1
    omega
  have hs_mono : StrictMono s := strictMono_nat_of_lt_succ hs_lt
  have hsum_ge : ∀ i, s (i + 1) - s i ≤ y i := fun i => by
    calc s (i + 1) - s i = (I i).card := (Nat.card_Ico _ _).symm
      _ = ∑ _ ∈ I i, 1 := by simp
      _ ≤ ∑ j ∈ I i, b.get j := Finset.sum_le_sum fun j _ => hb1 j
  have hy_pos : ∀ i, 1 ≤ y i := fun i => by
    have h1 := hs_lt i
    have h2 := hsum_ge i
    omega
  have hy_mono : StrictMono y := strictMono_nat_of_lt_succ fun i => by
    have hle : y i ≤ ∑ j ∈ Finset.range (s (i + 1)), b.get j :=
      Finset.sum_le_sum_of_subset fun j hj => Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
    have hge : folkSt b (i + 2) - folkSt b (i + 1) ≤ y (i + 1) := hsum_ge (i + 1)
    have hdef : folkSt b (i + 2) =
        folkSt b (i + 1) + (∑ j ∈ Finset.range (s (i + 1)), b.get j) + 1 := rfl
    omega
  have hdisj_lt : ∀ {i i'}, i < i' → Disjoint (I i) (I i') := fun {i i'} h =>
    Finset.disjoint_left.mpr fun x hx1 hx2 => by
      have hle : s (i + 1) ≤ s i' := hs_mono.monotone (by omega : i + 1 ≤ i')
      have hx1' := Finset.mem_Ico.mp hx1
      have hx2' := Finset.mem_Ico.mp hx2
      omega
  have hdisj : ∀ (J : Finset ℕ), (J : Set ℕ).PairwiseDisjoint I := fun J i _ i' _ hne => by
    rcases lt_trichotomy i i' with h | rfl | h
    · exact hdisj_lt h
    · exact False.elim (hne rfl)
    · exact (hdisj_lt h).symm
  let A : Finset ℕ := (Finset.range k).image y
  let M : ℕ := A.sum id
  have hA_card : A.card = k := by
    rw [Finset.card_image_of_injective _ hy_mono.injective, Finset.card_range]
  have hA_icc : ∀ {N}, M ≤ N → A ∈ (Finset.Icc 1 N).powersetCard k := fun {N} hMN => by
    refine Finset.mem_powersetCard.mpr ⟨fun a ha => ?_, hA_card⟩
    rcases Finset.mem_image.mp ha with ⟨i, _, rfl⟩
    have hle : y i ≤ M := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) ha
    exact Finset.mem_Icc.mpr ⟨hy_pos i, le_trans hle hMN⟩
  have hsub_props : ∀ z ∈ OMA.S_erdos_531.subsetSums A, (1 ≤ z ∧ z ≤ M) ∧ z ∈ C := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨T, hT, rfl⟩
    have hT_ne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hT).1
    have hT_sub : T ⊆ A := Finset.mem_powerset.mp (Finset.mem_erase.mp hT).2
    rcases hT_ne with ⟨t, ht⟩
    rcases Finset.mem_image.mp (hT_sub ht) with ⟨i0, _, ht_eq⟩
    have hpos : 1 ≤ T.sum id := by
      have ht1 : 1 ≤ t := ht_eq ▸ hy_pos i0
      exact le_trans ht1 (Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) ht)
    have hleM : T.sum id ≤ M := Finset.sum_le_sum_of_subset hT_sub
    let J : Finset ℕ := (Finset.range k).filter fun i => y i ∈ T
    have hTJ : T = J.image y := by
      ext x
      simp only [J, Finset.mem_image, Finset.mem_filter]
      constructor
      · intro hx
        rcases Finset.mem_image.mp (hT_sub hx) with ⟨i, hi, rfl⟩
        exact ⟨i, ⟨hi, hx⟩, rfl⟩
      · rintro ⟨i, ⟨_, hyi⟩, rfl⟩
        exact hyi
    have hJI_ne : (J.biUnion I).Nonempty := by
      have hi0 : i0 ∈ J := by
        have h_in : y i0 ∈ J.image y := hTJ ▸ ht_eq ▸ ht
        rcases Finset.mem_image.mp h_in with ⟨i1, hi1, heq⟩
        exact hy_mono.injective heq ▸ hi1
      rcases Finset.nonempty_Ico.mpr (hs_lt i0) with ⟨j0, hj0⟩
      exact ⟨j0, Finset.mem_biUnion.mpr ⟨i0, hi0, hj0⟩⟩
    have hsum_eq : T.sum id = ∑ j ∈ J.biUnion I, b.get j := by
      rw [hTJ, Finset.sum_image fun _ _ _ _ h => hy_mono.injective h]
      exact (Finset.sum_biUnion (hdisj J)).symm
    exact ⟨⟨hpos, hleM⟩, hb (hsum_eq ▸ Hindman.FS.finsetSum b (J.biUnion I) hJI_ne)⟩
  have hM_mem : {N : ℕ | M ≤ N} ∈ (U : Filter ℕ) :=
    Ultrafilter.of_le Filter.atTop (Filter.mem_atTop M)
  rcases Set.mem_insert_iff.mp hCS with rfl | hC1
  · have hall : (⋂ z ∈ OMA.S_erdos_531.subsetSums A, {N | z ∈ red N}) ∈ (U : Filter ℕ) :=
      (Filter.biInter_finset_mem _).mpr fun z hz => (hsub_props z hz).2.2
    obtain ⟨N, hMN, hNred⟩ := Filter.nonempty_of_mem (Filter.inter_mem hM_mem hall)
    exact havoid N A (hA_icc hMN) (Or.inl fun z hz => Set.mem_iInter₂.mp hNred z hz)
  · rw [Set.mem_singleton_iff.mp hC1] at hsub_props
    have hall : (⋂ z ∈ OMA.S_erdos_531.subsetSums A, {N | z ∉ red N}) ∈ (U : Filter ℕ) :=
      (Filter.biInter_finset_mem _).mpr fun z hz => (hsub_props z hz).2.2
    obtain ⟨N, hMN, hNblue⟩ := Filter.nonempty_of_mem (Filter.inter_mem hM_mem hall)
    refine havoid N A (hA_icc hMN) (Or.inr fun z hz => Finset.mem_sdiff.mpr ⟨?_, ?_⟩)
    · exact Finset.mem_Icc.mpr ⟨(hsub_props z hz).1.1, le_trans (hsub_props z hz).1.2 hMN⟩
    · exact Set.mem_iInter₂.mp hNblue z hz

private lemma folk_forces_mono {k M N : ℕ} (hMN : M ≤ N)
    (hM : OMA.S_erdos_531.ForcesMonoSums k M) :
    OMA.S_erdos_531.ForcesMonoSums k N := by
  intro red _
  have hsub : Finset.Icc 1 M ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc_right hMN
  rcases hM (red ∩ Finset.Icc 1 M) (Finset.mem_powerset.mpr Finset.inter_subset_right) with
    ⟨A, hA, h1 | h2⟩
  · exact ⟨A, Finset.powersetCard_mono hsub hA, Or.inl (h1.trans Finset.inter_subset_left)⟩
  · refine ⟨A, Finset.powersetCard_mono hsub hA, Or.inr (h2.trans fun x hx => ?_)⟩
    rw [Finset.mem_sdiff, Finset.mem_inter] at hx
    exact Finset.mem_sdiff.mpr ⟨hsub hx.1, fun hr => hx.2 ⟨hr, hx.1⟩⟩

private lemma folk_isLeast (k : ℕ) :
    IsLeast {N : ℕ | OMA.S_erdos_531.ForcesMonoSums k N} (OMA.S_erdos_531.folkmanNumber k) :=
  ⟨Nat.sInf_mem (folk_exists_forces k), fun _ h => Nat.sInf_le h⟩

private lemma folk_boundsFrom_iff (k₀ : ℕ) (lower upper : ℕ → ℕ) :
    OMA.S_erdos_531.BoundsFrom k₀ lower upper ↔
      ∀ k ≥ k₀, ¬ OMA.S_erdos_531.ForcesMonoSums k (lower k) ∧
        OMA.S_erdos_531.ForcesMonoSums k (upper k) := by
  unfold OMA.S_erdos_531.BoundsFrom
  refine forall₂_congr fun k _ => ?_
  obtain ⟨h_mem, h_le⟩ := folk_isLeast k
  exact ⟨fun ⟨hlt, hup⟩ => ⟨fun hF => not_le_of_gt hlt (h_le hF), folk_forces_mono hup h_mem⟩,
    fun ⟨hnF, hup⟩ => ⟨lt_of_not_ge fun hle => hnF (folk_forces_mono hle h_mem), h_le hup⟩⟩

theorem OMA.solution : type_of% @OMA.S_erdos_531.main := by
  exact ⟨fun k _ => folk_isLeast k, fun k₀ lower upper _ => folk_boundsFrom_iff k₀ lower upper⟩
