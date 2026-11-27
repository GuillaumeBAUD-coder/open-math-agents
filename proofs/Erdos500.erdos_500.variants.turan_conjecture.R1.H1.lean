import OMAReductions.R_Erdos500_erdos_500_variants_turan_conjecture_R1

-- Step Erdos500.erdos_500.variants.turan_conjecture.R1.H1
-- Credit: @caa1982

open Filter Finset

private def part (n : ℕ) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v : Fin n => v.val % 3 = r

private def turanEdges (n : ℕ) : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard 3).filter fun e =>
    let c0 := (e ∩ part n 0).card
    let c1 := (e ∩ part n 1).card
    let c2 := (e ∩ part n 2).card
    (c0 = 1 ∧ c1 = 1 ∧ c2 = 1) ∨
    (c0 = 2 ∧ c1 = 1 ∧ c2 = 0) ∨
    (c0 = 0 ∧ c1 = 2 ∧ c2 = 1) ∨
    (c0 = 1 ∧ c1 = 0 ∧ c2 = 2)

private lemma part_disjoint {n r s : ℕ} (hrs : r ≠ s) :
    Disjoint (part n r) (part n s) := by
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  simp only [part, Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
  exact hrs (hv1.symm.trans hv2)

private lemma card_inter_parts_sum {n : ℕ} (S : Finset (Fin n)) :
    (S ∩ part n 0).card + (S ∩ part n 1).card + (S ∩ part n 2).card = S.card := by
  have hunion : (S ∩ part n 0) ∪ (S ∩ part n 1) ∪ (S ∩ part n 2) = S := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, part, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    · intro hv
      have hmod : v.val % 3 = 0 ∨ v.val % 3 = 1 ∨ v.val % 3 = 2 := by omega
      rcases hmod with h | h | h
      · exact Or.inl (Or.inl ⟨hv, h⟩)
      · exact Or.inl (Or.inr ⟨hv, h⟩)
      · exact Or.inr ⟨hv, h⟩
  have hd01 : Disjoint (S ∩ part n 0) (S ∩ part n 1) :=
    (part_disjoint (by omega)).mono Finset.inter_subset_right Finset.inter_subset_right
  have hd012 : Disjoint ((S ∩ part n 0) ∪ (S ∩ part n 1)) (S ∩ part n 2) := by
    rw [Finset.disjoint_union_left]
    exact ⟨(part_disjoint (by omega)).mono Finset.inter_subset_right Finset.inter_subset_right,
      (part_disjoint (by omega)).mono Finset.inter_subset_right Finset.inter_subset_right⟩
  calc (S ∩ part n 0).card + (S ∩ part n 1).card + (S ∩ part n 2).card
      = ((S ∩ part n 0) ∪ (S ∩ part n 1) ∪ (S ∩ part n 2)).card := by
        rw [Finset.card_union_of_disjoint hd012, Finset.card_union_of_disjoint hd01]
    _ = S.card := by rw [hunion]

private lemma card_part_ge (n r : ℕ) (hr : r < 3) : n / 3 ≤ (part n r).card := by
  let f : Fin (n / 3) → Fin n := fun i => ⟨3 * i.val + r, by omega⟩
  have hcard : (Finset.univ.image f).card ≤ (part n r).card := by
    apply Finset.card_le_card
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    simp only [part, Finset.mem_filter, Finset.mem_univ, true_and, f]
    omega
  have hinj : Function.Injective f := by
    intro i j h
    have := congrArg Fin.val h
    simp only [f] at this
    exact Fin.ext (by omega)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_fin] at hcard
  exact hcard

private lemma turanEdges_free (n : ℕ) : ¬ (turanEdges n).ContainsCompleteHypergraph 3 4 := by
  rintro ⟨S, hScard, hSsub⟩
  have hsum := card_inter_parts_sum S
  rw [hScard] at hsum
  have hno_mono : ∀ r ∈ ({0, 1, 2} : Finset ℕ), (S ∩ part n r).card < 3 := by
    intro r hr
    by_contra! hge
    obtain ⟨e, hesub, hecard⟩ := Finset.exists_subset_card_eq hge
    have heS : e ∈ S.powersetCard 3 :=
      Finset.mem_powersetCard.mpr ⟨hesub.trans Finset.inter_subset_left, hecard⟩
    have heT := hSsub heS
    have he_part : e ∩ part n r = e := Finset.inter_eq_left.mpr (hesub.trans Finset.inter_subset_right)
    have hcr : (e ∩ part n r).card = 3 := by rw [he_part, hecard]
    simp only [turanEdges, Finset.mem_filter] at heT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl <;> omega
  have hc0 : (S ∩ part n 0).card ≤ 2 := Nat.lt_succ_iff.mp (hno_mono 0 (by simp))
  have hc1 : (S ∩ part n 1).card ≤ 2 := Nat.lt_succ_iff.mp (hno_mono 1 (by simp))
  have hc2 : (S ∩ part n 2).card ≤ 2 := Nat.lt_succ_iff.mp (hno_mono 2 (by simp))
  have hbad : ∀ r s : ℕ, r ≠ s →
      (r = 0 ∧ s = 2 ∨ r = 1 ∧ s = 0 ∨ r = 2 ∧ s = 1) →
      2 ≤ (S ∩ part n r).card → 1 ≤ (S ∩ part n s).card → False := by
    intro r s hrs hpair h2 h1
    obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq h2
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (S ∩ part n s).card)
    have hb_not_A : b ∉ A := by
      intro hbA
      have := (Finset.mem_inter.mp (hAsub hbA)).2
      have := (Finset.mem_inter.mp hb).2
      exact Finset.disjoint_left.mp (part_disjoint hrs) ‹_› ‹_›
    let e := insert b A
    have hecard : e.card = 3 := by rw [Finset.card_insert_of_notMem hb_not_A, hAcard]
    have hesub : e ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxA
      · exact (Finset.mem_inter.mp hb).1
      · exact (Finset.mem_inter.mp (hAsub hxA)).1
    have heT := hSsub (Finset.mem_powersetCard.mpr ⟨hesub, hecard⟩)
    have he_r : e ∩ part n r = A := by
      ext x
      simp only [e, Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hxA, hxr⟩
        · exfalso
          exact Finset.disjoint_left.mp (part_disjoint hrs) hxr (Finset.mem_inter.mp hb).2
        · exact hxA
      · intro hxA
        exact ⟨Or.inr hxA, (Finset.mem_inter.mp (hAsub hxA)).2⟩
    have he_s : e ∩ part n s = {b} := by
      ext x
      simp only [e, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | hxA, hxs⟩
        · rfl
        · exfalso
          exact Finset.disjoint_left.mp (part_disjoint hrs) (Finset.mem_inter.mp (hAsub hxA)).2 hxs
      · rintro rfl
        exact ⟨Or.inl rfl, (Finset.mem_inter.mp hb).2⟩
    have hcr : (e ∩ part n r).card = 2 := by rw [he_r, hAcard]
    have hcs : (e ∩ part n s).card = 1 := by rw [he_s, Finset.card_singleton]
    simp only [turanEdges, Finset.mem_filter] at heT
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  by_cases h02 : 2 ≤ (S ∩ part n 0).card ∧ 1 ≤ (S ∩ part n 2).card
  · exact hbad 0 2 (by omega) (Or.inl ⟨rfl, rfl⟩) h02.1 h02.2
  by_cases h10 : 2 ≤ (S ∩ part n 1).card ∧ 1 ≤ (S ∩ part n 0).card
  · exact hbad 1 0 (by omega) (Or.inr (Or.inl ⟨rfl, rfl⟩)) h10.1 h10.2
  by_cases h21 : 2 ≤ (S ∩ part n 2).card ∧ 1 ≤ (S ∩ part n 1).card
  · exact hbad 2 1 (by omega) (Or.inr (Or.inr ⟨rfl, rfl⟩)) h21.1 h21.2
  omega

private lemma card_pair_single {n r s : ℕ} (hrs : r ≠ s) :
    ((part n r).card.choose 2) * (part n s).card ≤
      (((Finset.univ : Finset (Fin n)).powersetCard 3).filter fun e =>
        (e ∩ part n r).card = 2 ∧ (e ∩ part n s).card = 1).card := by
  let S := (part n r).powersetCard 2 ×ˢ part n s
  let f : Finset (Fin n) × Fin n → Finset (Fin n) := fun p => insert p.2 p.1
  have hsub : S.image f ⊆ ((Finset.univ : Finset (Fin n)).powersetCard 3).filter fun e =>
      (e ∩ part n r).card = 2 ∧ (e ∩ part n s).card = 1 := by
    intro e he
    obtain ⟨⟨A, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hA, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hAsub, hAcard⟩ := Finset.mem_powersetCard.mp hA
    have hb_not : b ∉ A := fun h => Finset.disjoint_left.mp (part_disjoint hrs) (hAsub h) hb
    have hcard3 : (insert b A).card = 3 := by rw [Finset.card_insert_of_notMem hb_not, hAcard]
    have her : insert b A ∩ part n r = A := by
      ext x; simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hxA, hxr⟩
        · exact (Finset.disjoint_left.mp (part_disjoint hrs) hxr hb).elim
        · exact hxA
      · intro hxA; exact ⟨Or.inr hxA, hAsub hxA⟩
    have hes : insert b A ∩ part n s = {b} := by
      ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | hxA, hxs⟩
        · rfl
        · exact (Finset.disjoint_left.mp (part_disjoint hrs) (hAsub hxA) hxs).elim
      · rintro rfl; exact ⟨Or.inl rfl, hb⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard3⟩,
      by rw [her, hAcard], by rw [hes, Finset.card_singleton]⟩
  have hinj : Set.InjOn f (S : Set (Finset (Fin n) × Fin n)) := by
    rintro ⟨A₁, b₁⟩ h₁ ⟨A₂, b₂⟩ h₂ heq
    obtain ⟨hA₁, hb₁⟩ := Finset.mem_product.mp h₁
    obtain ⟨hA₂, hb₂⟩ := Finset.mem_product.mp h₂
    have hA₁sub := (Finset.mem_powersetCard.mp hA₁).1
    have hA₂sub := (Finset.mem_powersetCard.mp hA₂).1
    have hAeq : A₁ = A₂ := by
      have := congrArg (fun e => e ∩ part n r) heq
      have hr1 : insert b₁ A₁ ∩ part n r = A₁ := by
        ext x; simp only [Finset.mem_inter, Finset.mem_insert]
        exact ⟨fun ⟨hx, hxr⟩ => hx.elim (fun h => (Finset.disjoint_left.mp (part_disjoint hrs) (h ▸ hxr) hb₁).elim) id,
          fun hx => ⟨Or.inr hx, hA₁sub hx⟩⟩
      have hr2 : insert b₂ A₂ ∩ part n r = A₂ := by
        ext x; simp only [Finset.mem_inter, Finset.mem_insert]
        exact ⟨fun ⟨hx, hxr⟩ => hx.elim (fun h => (Finset.disjoint_left.mp (part_disjoint hrs) (h ▸ hxr) hb₂).elim) id,
          fun hx => ⟨Or.inr hx, hA₂sub hx⟩⟩
      simpa only [f, hr1, hr2] using this
    have hbeq : b₁ = b₂ := by
      have := congrArg (fun e => e ∩ part n s) heq
      have hs1 : insert b₁ A₁ ∩ part n s = {b₁} := by
        ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun ⟨hx, hxs⟩ => hx.elim id (fun h => (Finset.disjoint_left.mp (part_disjoint hrs) (hA₁sub h) hxs).elim),
          fun h => ⟨Or.inl h, h ▸ hb₁⟩⟩
      have hs2 : insert b₂ A₂ ∩ part n s = {b₂} := by
        ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun ⟨hx, hxs⟩ => hx.elim id (fun h => (Finset.disjoint_left.mp (part_disjoint hrs) (hA₂sub h) hxs).elim),
          fun h => ⟨Or.inl h, h ▸ hb₂⟩⟩
      have hsing : ({b₁} : Finset (Fin n)) = {b₂} := by simpa only [f, hs1, hs2] using this
      exact Finset.singleton_injective hsing
    exact Prod.ext hAeq hbeq
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_powersetCard] at hcard
  exact hcard

private lemma card_triple_one_each (n : ℕ) :
    (part n 0).card * (part n 1).card * (part n 2).card ≤
      (((Finset.univ : Finset (Fin n)).powersetCard 3).filter fun e =>
        (e ∩ part n 0).card = 1 ∧ (e ∩ part n 1).card = 1 ∧ (e ∩ part n 2).card = 1).card := by
  let S := (part n 0 ×ˢ part n 1) ×ˢ part n 2
  let f : (Fin n × Fin n) × Fin n → Finset (Fin n) := fun p => {p.1.1, p.1.2, p.2}
  have hsub : S.image f ⊆ ((Finset.univ : Finset (Fin n)).powersetCard 3).filter fun e =>
      (e ∩ part n 0).card = 1 ∧ (e ∩ part n 1).card = 1 ∧ (e ∩ part n 2).card = 1 := by
    intro e he
    obtain ⟨⟨⟨a, b⟩, c⟩, habc, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hab, hc⟩ := Finset.mem_product.mp habc
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    have hab_ne : a ≠ b := fun h => Finset.disjoint_left.mp (part_disjoint (by omega : 0 ≠ 1)) ha (h ▸ hb)
    have hac_ne : a ≠ c := fun h => Finset.disjoint_left.mp (part_disjoint (by omega : 0 ≠ 2)) ha (h ▸ hc)
    have hbc_ne : b ≠ c := fun h => Finset.disjoint_left.mp (part_disjoint (by omega : 1 ≠ 2)) hb (h ▸ hc)
    have hcard3 : ({a, b, c} : Finset (Fin n)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab_ne, hac_ne]),
        Finset.card_insert_of_notMem (by simp [hbc_ne]), Finset.card_singleton]
    have h0 : ({a, b, c} : Finset (Fin n)) ∩ part n 0 = {a} := by
      ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, hx⟩
        · rfl
        · exact (Finset.disjoint_left.mp (part_disjoint (by omega : 0 ≠ 1)) hx hb).elim
        · exact (Finset.disjoint_left.mp (part_disjoint (by omega : 0 ≠ 2)) hx hc).elim
      · rintro rfl; exact ⟨Or.inl rfl, ha⟩
    have h1 : ({a, b, c} : Finset (Fin n)) ∩ part n 1 = {b} := by
      ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, hx⟩
        · exact (Finset.disjoint_left.mp (part_disjoint (by omega : 1 ≠ 0)) hx ha).elim
        · rfl
        · exact (Finset.disjoint_left.mp (part_disjoint (by omega : 1 ≠ 2)) hx hc).elim
      · rintro rfl; exact ⟨Or.inr (Or.inl rfl), hb⟩
    have h2 : ({a, b, c} : Finset (Fin n)) ∩ part n 2 = {c} := by
      ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, hx⟩
        · exact (Finset.disjoint_left.mp (part_disjoint (by omega : 2 ≠ 0)) hx ha).elim
        · exact (Finset.disjoint_left.mp (part_disjoint (by omega : 2 ≠ 1)) hx hb).elim
        · rfl
      · rintro rfl; exact ⟨Or.inr (Or.inr rfl), hc⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard3⟩,
      by rw [h0, Finset.card_singleton], by rw [h1, Finset.card_singleton],
      by rw [h2, Finset.card_singleton]⟩
  have hinj : Set.InjOn f (S : Set ((Fin n × Fin n) × Fin n)) := by
    rintro ⟨⟨a₁, b₁⟩, c₁⟩ h₁ ⟨⟨a₂, b₂⟩, c₂⟩ h₂ heq
    dsimp only [f] at heq
    obtain ⟨hab₁, hc₁⟩ := Finset.mem_product.mp h₁
    obtain ⟨ha₁, hb₁⟩ := Finset.mem_product.mp hab₁
    obtain ⟨hab₂, hc₂⟩ := Finset.mem_product.mp h₂
    obtain ⟨ha₂, hb₂⟩ := Finset.mem_product.mp hab₂
    have ha : a₁ = a₂ := by
      have hmem : a₁ ∈ ({a₂, b₂, c₂} : Finset (Fin n)) := heq ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · rfl
      · exact (Finset.disjoint_left.mp (part_disjoint (by omega : 0 ≠ 1)) ha₁ hb₂).elim
      · exact (Finset.disjoint_left.mp (part_disjoint (by omega : 0 ≠ 2)) ha₁ hc₂).elim
    have hb : b₁ = b₂ := by
      have hmem : b₁ ∈ ({a₂, b₂, c₂} : Finset (Fin n)) := heq ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact (Finset.disjoint_left.mp (part_disjoint (by omega : 1 ≠ 0)) hb₁ ha₂).elim
      · rfl
      · exact (Finset.disjoint_left.mp (part_disjoint (by omega : 1 ≠ 2)) hb₁ hc₂).elim
    have hc : c₁ = c₂ := by
      have hmem : c₁ ∈ ({a₂, b₂, c₂} : Finset (Fin n)) := heq ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact (Finset.disjoint_left.mp (part_disjoint (by omega : 2 ≠ 0)) hc₁ ha₂).elim
      · exact (Finset.disjoint_left.mp (part_disjoint (by omega : 2 ≠ 1)) hc₁ hb₂).elim
      · rfl
    exact Prod.ext (Prod.ext ha hb) hc
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_product] at hcard
  exact hcard

private lemma turanEdges_card_ge (n : ℕ) :
    let m := n / 3
    m ^ 3 + 3 * (m.choose 2 * m) ≤ (turanEdges n).card := by
  intro m
  let U := (Finset.univ : Finset (Fin n)).powersetCard 3
  let E111 := U.filter fun e => (e ∩ part n 0).card = 1 ∧ (e ∩ part n 1).card = 1 ∧ (e ∩ part n 2).card = 1
  let E210 := U.filter fun e => (e ∩ part n 0).card = 2 ∧ (e ∩ part n 1).card = 1
  let E021 := U.filter fun e => (e ∩ part n 1).card = 2 ∧ (e ∩ part n 2).card = 1
  let E102 := U.filter fun e => (e ∩ part n 2).card = 2 ∧ (e ∩ part n 0).card = 1
  have hsub : E111 ∪ E210 ∪ E021 ∪ E102 ⊆ turanEdges n := by
    intro e he
    simp only [Finset.mem_union] at he
    have heU : e ∈ U := by
      rcases he with ((h | h) | h) | h <;> exact (Finset.mem_filter.mp h).1
    have hsum : (e ∩ part n 0).card + (e ∩ part n 1).card + (e ∩ part n 2).card = 3 := by
      rw [card_inter_parts_sum, (Finset.mem_powersetCard.mp heU).2]
    refine Finset.mem_filter.mpr ⟨heU, ?_⟩
    rcases he with ((h | h) | h) | h
    · exact Or.inl (Finset.mem_filter.mp h).2
    · obtain ⟨h0, h1⟩ := (Finset.mem_filter.mp h).2
      exact Or.inr (Or.inl ⟨h0, h1, by omega⟩)
    · obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp h).2
      exact Or.inr (Or.inr (Or.inl ⟨by omega, h1, h2⟩))
    · obtain ⟨h2, h0⟩ := (Finset.mem_filter.mp h).2
      exact Or.inr (Or.inr (Or.inr ⟨h0, by omega, h2⟩))
  have hd1 : Disjoint E111 E210 := by
    rw [Finset.disjoint_left]; intro e h1 h2
    have := (Finset.mem_filter.mp h1).2.1
    have := (Finset.mem_filter.mp h2).2.1; omega
  have hd2 : Disjoint (E111 ∪ E210) E021 := by
    rw [Finset.disjoint_left]; intro e h1 h2
    have h2' := (Finset.mem_filter.mp h2).2.1
    rcases Finset.mem_union.mp h1 with h | h
    · have := (Finset.mem_filter.mp h).2.2.1; omega
    · have := (Finset.mem_filter.mp h).2.2; omega
  have hd3 : Disjoint (E111 ∪ E210 ∪ E021) E102 := by
    rw [Finset.disjoint_left]; intro e h1 h2
    have h2' := (Finset.mem_filter.mp h2).2.1
    rcases Finset.mem_union.mp h1 with h | h
    · rcases Finset.mem_union.mp h with h | h
      · have := (Finset.mem_filter.mp h).2.2.2; omega
      · have heU := (Finset.mem_filter.mp h).1
        have hsum : (e ∩ part n 0).card + (e ∩ part n 1).card + (e ∩ part n 2).card = 3 := by
          rw [card_inter_parts_sum, (Finset.mem_powersetCard.mp heU).2]
        have := (Finset.mem_filter.mp h).2.1
        have := (Finset.mem_filter.mp h).2.2; omega
    · have := (Finset.mem_filter.mp h).2.2; omega
  have hcard : E111.card + E210.card + E021.card + E102.card ≤ (turanEdges n).card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd2,
      Finset.card_union_of_disjoint hd1] at this
  have h0 : m ≤ (part n 0).card := card_part_ge n 0 (by omega)
  have h1 : m ≤ (part n 1).card := card_part_ge n 1 (by omega)
  have h2 : m ≤ (part n 2).card := card_part_ge n 2 (by omega)
  have hc111 : m ^ 3 ≤ E111.card := by
    have := card_triple_one_each n
    calc m ^ 3 = m * m * m := by ring
      _ ≤ (part n 0).card * (part n 1).card * (part n 2).card :=
          Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2
      _ ≤ E111.card := this
  have hc210 : m.choose 2 * m ≤ E210.card :=
    (Nat.mul_le_mul (Nat.choose_le_choose 2 h0) h1).trans (card_pair_single (by omega))
  have hc021 : m.choose 2 * m ≤ E021.card :=
    (Nat.mul_le_mul (Nat.choose_le_choose 2 h1) h2).trans (card_pair_single (by omega))
  have hc102 : m.choose 2 * m ≤ E102.card :=
    (Nat.mul_le_mul (Nat.choose_le_choose 2 h2) h0).trans (card_pair_single (by omega))
  omega

theorem OMA.solution : OMA.R_Erdos500_erdos_500_variants_turan_conjecture_R1.H1 := by
  classical
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (100 / ε)
  filter_upwards [eventually_ge_atTop (max N 30)] with n hn
  have hNle : N ≤ n := le_trans (le_max_left _ _) hn
  have hn30 : 30 ≤ n := le_trans (le_max_right _ _) hn
  have hle_ext : (turanEdges n).card ≤ Hypergraph.cliqueExtremalNumber n 3 4 := by
    unfold Hypergraph.cliqueExtremalNumber
    refine Finset.le_sup (f := Finset.card) ?_
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.filter_subset _ _, turanEdges_free n⟩
  let m := n / 3
  have hm_ge : 10 ≤ m := by omega
  have hcard : m ^ 3 + 3 * (m.choose 2 * m) ≤ (turanEdges n).card := turanEdges_card_ge n
  have h2card : 5 * m ^ 3 ≤ 2 * (turanEdges n).card + 3 * m ^ 2 := by
    have hch : 2 * m.choose 2 = m * (m - 1) := by
      calc 2 * m.choose 2 = Nat.factorial 2 * m.choose 2 := rfl
        _ = m.descFactorial 2 := (Nat.descFactorial_eq_factorial_mul_choose m 2).symm
        _ = m * (m - 1) := by simp [Nat.descFactorial_succ]; ring
    have h1 : 2 * (m ^ 3 + 3 * (m.choose 2 * m)) = 2 * m ^ 3 + 3 * (m * (m - 1) * m) := by
      have : 2 * (m.choose 2 * m) = (2 * m.choose 2) * m := by ring
      rw [mul_add, ← mul_assoc, mul_comm 2 3, mul_assoc, this, hch]
    have h2 : m * (m - 1) * m + m ^ 2 = m ^ 3 := by
      cases m with
      | zero => omega
      | succ k => simp only [Nat.add_sub_cancel]; ring
    omega
  have h2cardR : 5 * (m : ℝ) ^ 3 ≤ 2 * ((turanEdges n).card : ℝ) + 3 * (m : ℝ) ^ 2 := by
    exact_mod_cast h2card
  have hchooseR : 6 * (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 := by
    have h6 : 6 * n.choose 3 ≤ n ^ 3 := by
      have hdesc : n.choose 3 * 6 = n * (n - 1) * (n - 2) := by
        rw [show (6 : ℕ) = Nat.factorial 3 by decide, mul_comm,
          ← Nat.descFactorial_eq_factorial_mul_choose,
          Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_one]
        ring
      have h1 : n - 1 ≤ n := Nat.sub_le _ _
      have h2 : n - 2 ≤ n := Nat.sub_le _ _
      have hprod : n * (n - 1) * (n - 2) ≤ n * n * n :=
        Nat.mul_le_mul (Nat.mul_le_mul_left n h1) h2
      have hpow : n * n * n = n ^ 3 := by ring
      omega
    exact_mod_cast h6
  have hm_rel : (n : ℝ) - 2 ≤ 3 * (m : ℝ) := by
    have : n ≤ 3 * m + 2 := by omega
    have : (n : ℝ) ≤ 3 * (m : ℝ) + 2 := by exact_mod_cast this
    linarith
  have hm_le : 3 * (m : ℝ) ≤ (n : ℝ) := by
    have : 3 * m ≤ n := by omega
    exact_mod_cast this
  have hn_pos : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn30
  have hεn : 100 < ε * (n : ℝ) := by
    have h1 : 100 / ε < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hNle)
    linarith [(div_lt_iff₀ hε).mp h1]
  have hcube : ((n : ℝ) - 2) ^ 3 ≤ 27 * (m : ℝ) ^ 3 := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ (n : ℝ) - 2) hm_rel 3
    linarith
  have hm2 : 9 * (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hextR : ((turanEdges n).card : ℝ) ≤ (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := by
    exact_mod_cast hle_ext
  have hfinal : (5 / 9 - ε) * ((n : ℝ) ^ 3 / 6) ≤ ((turanEdges n).card : ℝ) := by
    have hdiff : 5 * (n : ℝ) ^ 3 - 54 * ((turanEdges n).card : ℝ) ≤ 39 * (n : ℝ) ^ 2 := by
      nlinarith [hcube, h2cardR, hm2]
    nlinarith [mul_le_mul_of_nonneg_right hεn.le (sq_nonneg (n : ℝ))]
  have hch_nonneg : (0 : ℝ) ≤ (n.choose 3 : ℝ) := Nat.cast_nonneg _
  by_cases h59 : 5 / 9 - ε ≤ 0
  · have h1 : (5 / 9 - ε) * (n.choose 3 : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h59 hch_nonneg
    have h2 : (0 : ℝ) ≤ (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := Nat.cast_nonneg _
    linarith
  · push Not at h59
    have hch_le : (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 / 6 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hch_le h59.le
    linarith
