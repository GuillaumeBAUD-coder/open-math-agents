import FormalConjectures.ErdosProblems.«500»

-- Problem: Erdős Problem 500 — lower bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/500.lean:63 (declaration Erdos500.erdos_500.variants.lower_bound)
-- Credit: @michielkosters (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter

private def col {n : ℕ} (v : Fin n) : Fin 3 :=
  ⟨v.val % 3, Nat.mod_lt _ (by omega)⟩

private def cnt {n : ℕ} (e : Finset (Fin n)) (i : Fin 3) : ℕ :=
  (e.filter (fun v => col v = i)).card

private def isGood {n : ℕ} (e : Finset (Fin n)) : Prop :=
  e.card = 3 ∧
    ((cnt e 0 = 1 ∧ cnt e 1 = 1 ∧ cnt e 2 = 1) ∨
     (cnt e 0 = 2 ∧ cnt e 1 = 1) ∨
     (cnt e 1 = 2 ∧ cnt e 2 = 1) ∨
     (cnt e 2 = 2 ∧ cnt e 0 = 1))

section
open scoped Classical

private noncomputable def turanH (n : ℕ) : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard 3).filter isGood

private lemma cnt_sum {n : ℕ} (S : Finset (Fin n)) :
    cnt S 0 + cnt S 1 + cnt S 2 = S.card := by
  simp only [cnt, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  trans ∑ _v ∈ S, 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    have h012 : col v = 0 ∨ col v = 1 ∨ col v = 2 := by
      rcases col v with ⟨k, hk⟩
      interval_cases k <;> simp
    rcases h012 with h | h | h <;> simp [h]
  · simp

private lemma cnt_erase {n : ℕ} {S : Finset (Fin n)} {v : Fin n} (hv : v ∈ S) (i : Fin 3) :
    cnt (S.erase v) i = cnt S i - if col v = i then 1 else 0 := by
  simp only [cnt]
  have hfilt : (S.erase v).filter (fun x => col x = i) =
      (S.filter (fun x => col x = i)).erase v := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  rw [hfilt]
  by_cases hvi : col v = i
  · have hmem : v ∈ S.filter (fun x => col x = i) := Finset.mem_filter.mpr ⟨hv, hvi⟩
    simp [hvi, Finset.card_erase_of_mem hmem]
  · simp [hvi]

private lemma turanH_no_k4 (n : ℕ) : ¬ (turanH n).ContainsCompleteHypergraph 3 4 := by
  rintro ⟨S, hS, hsub⟩
  have hsum : cnt S 0 + cnt S 1 + cnt S 2 = 4 := by rw [cnt_sum, hS]
  have erase_bad : ∀ j : Fin 3, 0 < cnt S j →
      let b0 := cnt S 0 - if j = 0 then 1 else 0
      let b1 := cnt S 1 - if j = 1 then 1 else 0
      let b2 := cnt S 2 - if j = 2 then 1 else 0
      (b0 = 1 ∧ b1 = 1 ∧ b2 = 1) ∨ (b0 = 2 ∧ b1 = 1) ∨
        (b1 = 2 ∧ b2 = 1) ∨ (b2 = 2 ∧ b0 = 1) := by
    intro j hj
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hj
    rw [Finset.mem_filter] at hv
    obtain ⟨hvS, hvj⟩ := hv
    have he : S.erase v ∈ turanH n := by
      apply hsub
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.erase_subset v S, by rw [Finset.card_erase_of_mem hvS, hS]⟩
    simp only [turanH, Finset.mem_filter] at he
    obtain ⟨_, _, hgood⟩ := he
    rwa [cnt_erase hvS 0, cnt_erase hvS 1, cnt_erase hvS 2, hvj] at hgood
  have h0 := erase_bad 0
  have h1 := erase_bad 1
  have h2 := erase_bad 2
  dsimp only at h0 h1 h2
  simp only [Fin.reduceEq, ↓reduceIte] at h0 h1 h2
  omega

private def partV (n : ℕ) (i : Fin 3) : Finset (Fin n) :=
  Finset.univ.filter (fun v => col v = i)

private lemma div_le_card_partV (n : ℕ) (i : Fin 3) : n / 3 ≤ (partV n i).card := by
  let f : Fin (n / 3) → Fin n := fun j => ⟨3 * j.val + i.val, by omega⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    ext
    have hval := congrArg Fin.val hab
    dsimp [f] at hval
    omega
  have hf_mem : ∀ j : Fin (n / 3), f j ∈ partV n i := by
    intro j
    rw [partV, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    ext
    dsimp [col, f]
    omega
  calc n / 3 = (Finset.univ : Finset (Fin (n / 3))).card := by simp
    _ = ((Finset.univ : Finset (Fin (n / 3))).image f).card :=
        (Finset.card_image_of_injective _ hf_inj).symm
    _ ≤ (partV n i).card := by
        apply Finset.card_le_card
        intro v hv
        rw [Finset.mem_image] at hv
        rcases hv with ⟨j, _, rfl⟩
        exact hf_mem j

private noncomputable def rainbowSet (n : ℕ) : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard 3).filter
    (fun e => cnt e 0 = 1 ∧ cnt e 1 = 1 ∧ cnt e 2 = 1)

private noncomputable def pairSet (n : ℕ) (i j : Fin 3) : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard 3).filter
    (fun e => cnt e i = 2 ∧ cnt e j = 1)

private lemma card_rainbowSet_ge (n : ℕ) :
    (partV n 0).card * (partV n 1).card * (partV n 2).card ≤ (rainbowSet n).card := by
  let T := (partV n 0 ×ˢ partV n 1) ×ˢ partV n 2
  let g : (Fin n × Fin n) × Fin n → Finset (Fin n) := fun p => {p.1.1, p.1.2, p.2}
  have hT : T.card = (partV n 0).card * (partV n 1).card * (partV n 2).card := by
    simp [T, Finset.card_product]
  rw [← hT]
  apply Finset.card_le_card_of_injOn g
  · intro p hp
    rcases p with ⟨⟨x, y⟩, z⟩
    simp only [T, Finset.mem_coe, Finset.mem_product, partV, Finset.mem_filter,
      Finset.mem_univ, true_and] at hp
    rcases hp with ⟨⟨hx, hy⟩, hz⟩
    have hxy : x ≠ y := by intro h; rw [h, hy] at hx; exact absurd hx (by decide)
    have hxz : x ≠ z := by intro h; rw [h, hz] at hx; exact absurd hx (by decide)
    have hyz : y ≠ z := by intro h; rw [h, hz] at hy; exact absurd hy (by decide)
    have hcard : (g ((x, y), z)).card = 3 := by
      dsimp [g]
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxz])]
      rw [Finset.card_insert_of_notMem (by simp [hyz])]
      simp
    have hcnt0 : cnt (g ((x, y), z)) 0 = 1 := by
      have hf : (g ((x, y), z)).filter (fun v => col v = 0) = {x} := by
        ext v
        simp only [g, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl | rfl, hv⟩
          · rfl
          · rw [hy] at hv; exact absurd hv (by decide)
          · rw [hz] at hv; exact absurd hv (by decide)
        · rintro rfl; exact ⟨Or.inl rfl, hx⟩
      simp [cnt, hf]
    have hcnt1 : cnt (g ((x, y), z)) 1 = 1 := by
      have hf : (g ((x, y), z)).filter (fun v => col v = 1) = {y} := by
        ext v
        simp only [g, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl | rfl, hv⟩
          · rw [hx] at hv; exact absurd hv (by decide)
          · rfl
          · rw [hz] at hv; exact absurd hv (by decide)
        · rintro rfl; exact ⟨Or.inr (Or.inl rfl), hy⟩
      simp [cnt, hf]
    have hcnt2 : cnt (g ((x, y), z)) 2 = 1 := by
      have hf : (g ((x, y), z)).filter (fun v => col v = 2) = {z} := by
        ext v
        simp only [g, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl | rfl, hv⟩
          · rw [hx] at hv; exact absurd hv (by decide)
          · rw [hy] at hv; exact absurd hv (by decide)
          · rfl
        · rintro rfl; exact ⟨Or.inr (Or.inr rfl), hz⟩
      simp [cnt, hf]
    simp only [rainbowSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    exact ⟨hcard, hcnt0, hcnt1, hcnt2⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    rcases p₁ with ⟨⟨x₁, y₁⟩, z₁⟩
    rcases p₂ with ⟨⟨x₂, y₂⟩, z₂⟩
    simp only [T, Finset.mem_coe, Finset.mem_product, partV, Finset.mem_filter,
      Finset.mem_univ, true_and] at hp₁ hp₂
    rcases hp₁ with ⟨⟨hx₁, hy₁⟩, hz₁⟩
    rcases hp₂ with ⟨⟨hx₂, hy₂⟩, hz₂⟩
    have hx : x₁ = x₂ := by
      have hmem : x₁ ∈ g ((x₂, y₂), z₂) := by rw [← heq]; simp [g]
      simp only [g, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · rfl
      · rw [hy₂] at hx₁; exact absurd hx₁ (by decide)
      · rw [hz₂] at hx₁; exact absurd hx₁ (by decide)
    have hy : y₁ = y₂ := by
      have hmem : y₁ ∈ g ((x₂, y₂), z₂) := by rw [← heq]; simp [g]
      simp only [g, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · rw [hx₂] at hy₁; exact absurd hy₁ (by decide)
      · rfl
      · rw [hz₂] at hy₁; exact absurd hy₁ (by decide)
    have hz : z₁ = z₂ := by
      have hmem : z₁ ∈ g ((x₂, y₂), z₂) := by rw [← heq]; simp [g]
      simp only [g, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · rw [hx₂] at hz₁; exact absurd hz₁ (by decide)
      · rw [hy₂] at hz₁; exact absurd hz₁ (by decide)
      · rfl
    subst hx; subst hy; subst hz; rfl

private lemma card_pairSet_ge (n : ℕ) {i j : Fin 3} (hij : i ≠ j) :
    (partV n i).card.choose 2 * (partV n j).card ≤ (pairSet n i j).card := by
  let T := (partV n i).powersetCard 2 ×ˢ partV n j
  let g : Finset (Fin n) × Fin n → Finset (Fin n) := fun p => insert p.2 p.1
  have hT : T.card = (partV n i).card.choose 2 * (partV n j).card := by
    simp [T, Finset.card_product, Finset.card_powersetCard]
  rw [← hT]
  apply Finset.card_le_card_of_injOn g
  · intro p hp
    rcases p with ⟨P, y⟩
    simp only [T, Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard,
      partV, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨⟨hPsub, hPcard⟩, hy⟩
    have hPcol : ∀ x ∈ P, col x = i := fun x hx =>
      (Finset.mem_filter.mp (hPsub hx)).2
    have hyP : y ∉ P := fun h => hij ((hPcol y h).symm.trans hy)
    have hcard : (g (P, y)).card = 3 := by
      dsimp [g]
      rw [Finset.card_insert_of_notMem hyP, hPcard]
    have hcnti : cnt (g (P, y)) i = 2 := by
      have hf : (g (P, y)).filter (fun v => col v = i) = P := by
        ext v
        simp only [g, Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hvP, hvi⟩
          · exact absurd (hy.symm.trans hvi) hij.symm
          · exact hvP
        · intro hvP; exact ⟨Or.inr hvP, hPcol v hvP⟩
      simp [cnt, hf, hPcard]
    have hcntj : cnt (g (P, y)) j = 1 := by
      have hf : (g (P, y)).filter (fun v => col v = j) = {y} := by
        ext v
        simp only [g, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | hvP, hvj⟩
          · rfl
          · exact absurd ((hPcol v hvP).symm.trans hvj) hij
        · rintro rfl; exact ⟨Or.inl rfl, hy⟩
      simp [cnt, hf]
    simp only [pairSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    exact ⟨hcard, hcnti, hcntj⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    rcases p₁ with ⟨P₁, y₁⟩
    rcases p₂ with ⟨P₂, y₂⟩
    simp only [T, Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard,
      partV, Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
    rcases hp₁ with ⟨⟨hP₁sub, _⟩, hy₁⟩
    rcases hp₂ with ⟨⟨hP₂sub, _⟩, hy₂⟩
    have hP₁col : ∀ x ∈ P₁, col x = i := fun x hx =>
      (Finset.mem_filter.mp (hP₁sub hx)).2
    have hP₂col : ∀ x ∈ P₂, col x = i := fun x hx =>
      (Finset.mem_filter.mp (hP₂sub hx)).2
    have hy₁P₁ : y₁ ∉ P₁ := fun h => hij ((hP₁col y₁ h).symm.trans hy₁)
    have hy₂P₂ : y₂ ∉ P₂ := fun h => hij ((hP₂col y₂ h).symm.trans hy₂)
    have hy_eq : y₁ = y₂ := by
      have hmem : y₁ ∈ g (P₂, y₂) := by rw [← heq]; simp [g]
      simp only [g, Finset.mem_insert] at hmem
      rcases hmem with rfl | hy₁P₂
      · rfl
      · exact absurd ((hP₂col y₁ hy₁P₂).symm.trans hy₁) hij
    subst hy_eq
    have hP_eq : P₁ = P₂ := by
      have := congrArg (fun s => s.erase y₁) heq
      dsimp [g] at this
      rwa [Finset.erase_insert hy₁P₁, Finset.erase_insert hy₂P₂] at this
    subst hP_eq
    rfl

private lemma card_turanH_ge (n : ℕ) :
    (n / 3) ^ 3 + 3 * ((n / 3).choose 2 * (n / 3)) ≤ (turanH n).card := by
  have hsub0 : rainbowSet n ⊆ turanH n := by
    intro e he
    simp only [rainbowSet, turanH, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and] at he ⊢
    exact ⟨he.1, he.1, Or.inl he.2⟩
  have hsub1 : pairSet n 0 1 ⊆ turanH n := by
    intro e he
    simp only [pairSet, turanH, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and] at he ⊢
    exact ⟨he.1, he.1, Or.inr (Or.inl he.2)⟩
  have hsub2 : pairSet n 1 2 ⊆ turanH n := by
    intro e he
    simp only [pairSet, turanH, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and] at he ⊢
    exact ⟨he.1, he.1, Or.inr (Or.inr (Or.inl he.2))⟩
  have hsub3 : pairSet n 2 0 ⊆ turanH n := by
    intro e he
    simp only [pairSet, turanH, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and] at he ⊢
    exact ⟨he.1, he.1, Or.inr (Or.inr (Or.inr he.2))⟩
  have hd01 : Disjoint (rainbowSet n) (pairSet n 0 1) := by
    rw [Finset.disjoint_left]
    intro e h0 h1
    simp only [rainbowSet, pairSet, Finset.mem_filter] at h0 h1
    omega
  have hd02 : Disjoint (rainbowSet n) (pairSet n 1 2) := by
    rw [Finset.disjoint_left]
    intro e h0 h2
    simp only [rainbowSet, pairSet, Finset.mem_filter] at h0 h2
    omega
  have hd03 : Disjoint (rainbowSet n) (pairSet n 2 0) := by
    rw [Finset.disjoint_left]
    intro e h0 h3
    simp only [rainbowSet, pairSet, Finset.mem_filter] at h0 h3
    omega
  have hd12 : Disjoint (pairSet n 0 1) (pairSet n 1 2) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [pairSet, Finset.mem_filter] at h1 h2
    omega
  have hd13 : Disjoint (pairSet n 0 1) (pairSet n 2 0) := by
    rw [Finset.disjoint_left]
    intro e h1 h3
    simp only [pairSet, Finset.mem_filter] at h1 h3
    omega
  have hd23 : Disjoint (pairSet n 1 2) (pairSet n 2 0) := by
    rw [Finset.disjoint_left]
    intro e h2 h3
    simp only [pairSet, Finset.mem_filter] at h2 h3
    omega
  have hU_sub : rainbowSet n ∪ pairSet n 0 1 ∪ pairSet n 1 2 ∪ pairSet n 2 0 ⊆ turanH n :=
    Finset.union_subset (Finset.union_subset (Finset.union_subset hsub0 hsub1) hsub2) hsub3
  have hU_card : (rainbowSet n ∪ pairSet n 0 1 ∪ pairSet n 1 2 ∪ pairSet n 2 0).card =
      (rainbowSet n).card + (pairSet n 0 1).card +
        (pairSet n 1 2).card + (pairSet n 2 0).card := by
    rw [Finset.card_union_of_disjoint
          (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hd03, hd13⟩, hd23⟩)]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd02, hd12⟩)]
    rw [Finset.card_union_of_disjoint hd01]
  have hq0 := div_le_card_partV n 0
  have hq1 := div_le_card_partV n 1
  have hq2 := div_le_card_partV n 2
  have hc0 : (n / 3) ^ 3 ≤ (rainbowSet n).card := by
    calc (n / 3) ^ 3 = (n / 3) * (n / 3) * (n / 3) := by ring
      _ ≤ (partV n 0).card * (partV n 1).card * (partV n 2).card :=
          Nat.mul_le_mul (Nat.mul_le_mul hq0 hq1) hq2
      _ ≤ (rainbowSet n).card := card_rainbowSet_ge n
  have hc1 : (n / 3).choose 2 * (n / 3) ≤ (pairSet n 0 1).card := by
    calc (n / 3).choose 2 * (n / 3) ≤ (partV n 0).card.choose 2 * (partV n 1).card :=
          Nat.mul_le_mul (Nat.choose_le_choose 2 hq0) hq1
      _ ≤ (pairSet n 0 1).card := card_pairSet_ge n (by decide)
  have hc2 : (n / 3).choose 2 * (n / 3) ≤ (pairSet n 1 2).card := by
    calc (n / 3).choose 2 * (n / 3) ≤ (partV n 1).card.choose 2 * (partV n 2).card :=
          Nat.mul_le_mul (Nat.choose_le_choose 2 hq1) hq2
      _ ≤ (pairSet n 1 2).card := card_pairSet_ge n (by decide)
  have hc3 : (n / 3).choose 2 * (n / 3) ≤ (pairSet n 2 0).card := by
    calc (n / 3).choose 2 * (n / 3) ≤ (partV n 2).card.choose 2 * (partV n 0).card :=
          Nat.mul_le_mul (Nat.choose_le_choose 2 hq2) hq0
      _ ≤ (pairSet n 2 0).card := card_pairSet_ge n (by decide)
  have hcard_le := Finset.card_le_card hU_sub
  rw [hU_card] at hcard_le
  omega

private lemma turanH_le_extremal (n : ℕ) :
    (turanH n).card ≤ Hypergraph.cliqueExtremalNumber n 3 4 := by
  unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
  apply Finset.le_sup
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.filter_subset _ _, turanH_no_k4 n⟩

end

private lemma choose_two_cast (m : ℕ) :
    (m.choose 2 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add, ih]
    push_cast
    ring

private lemma choose_three_cast (m : ℕ) :
    (m.choose 3 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.cast_add, ih, choose_two_cast]
    push_cast
    ring

private lemma choose_three_le (n : ℕ) : (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 / 6 := by
  by_cases hn : n ≤ 2
  · have h0 : n.choose 3 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h0]
    norm_num
    positivity
  · rw [choose_three_cast]
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 3 ≤ n)
    nlinarith

theorem OMA.solution : type_of% @Erdos500.erdos_500.variants.lower_bound := by
  intro ε hε
  by_cases hε_big : 5 / 9 ≤ ε
  · refine Eventually.of_forall fun n => ?_
    have h1 : 5 / 9 - ε ≤ 0 := by linarith
    have h2 : (0 : ℝ) ≤ (n.choose 3 : ℝ) := Nat.cast_nonneg _
    have h3 : (5 / 9 - ε) * (n.choose 3 : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 h2
    exact h3.trans (Nat.cast_nonneg _)
  · have hε_lt : ε < 5 / 9 := lt_of_not_ge hε_big
    obtain ⟨N, hN⟩ := exists_nat_ge (max 2 (6 / ε))
    rw [eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    have hn_r : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hN2 : (2 : ℝ) ≤ (n : ℝ) := le_trans (le_max_left _ _) (le_trans hN hn_r)
    have hNε : 6 / ε ≤ (n : ℝ) := le_trans (le_max_right _ _) (le_trans hN hn_r)
    have hpos_coef : 0 < (5 / 9 - ε : ℝ) := by linarith
    have h_upper : (5 / 9 - ε) * (n.choose 3 : ℝ) ≤ (5 / 9 - ε) * ((n : ℝ) ^ 3 / 6) :=
      mul_le_mul_of_nonneg_left (choose_three_le n) hpos_coef.le
    have hεn : (n : ℝ) ^ 2 ≤ (ε / 6) * (n : ℝ) ^ 3 := by
      have h6 : 6 ≤ ε * (n : ℝ) := by rw [div_le_iff₀ hε] at hNε; linarith
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
      nlinarith [sq_nonneg (n : ℝ)]
    have h_poly : (5 / 9 - ε) * ((n : ℝ) ^ 3 / 6) ≤
        (5 / 2 : ℝ) * (((n : ℝ) - 2) / 3) ^ 3 - (3 / 2 : ℝ) * ((n : ℝ) / 3) ^ 2 := by
      have h_id : (5 / 2 : ℝ) * (((n : ℝ) - 2) / 3) ^ 3 - (3 / 2 : ℝ) * ((n : ℝ) / 3) ^ 2 =
          (5 / 54 : ℝ) * (n : ℝ) ^ 3 - (13 / 18 : ℝ) * (n : ℝ) ^ 2 +
            (10 / 9 : ℝ) * (n : ℝ) - 20 / 27 := by ring
      rw [h_id]
      have h_rem : (13 / 18 : ℝ) * (n : ℝ) ^ 2 - (10 / 9 : ℝ) * (n : ℝ) + 20 / 27 ≤
          (n : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (n : ℝ)]
      linarith
    have hdiv : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm
    have hmod_lt : n % 3 ≤ 2 := Nat.lt_succ_iff.mp (Nat.mod_lt n (by omega))
    have hdiv_r : (n : ℝ) = 3 * ((n / 3 : ℕ) : ℝ) + ((n % 3 : ℕ) : ℝ) := by
      exact_mod_cast hdiv
    have hmod_nonneg : (0 : ℝ) ≤ ((n % 3 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hmod_le : ((n % 3 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hmod_lt
    have hq_lo : ((n : ℝ) - 2) / 3 ≤ ((n / 3 : ℕ) : ℝ) := by linarith
    have hq_hi : ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) / 3 := by linarith
    have hq_nonneg : (0 : ℝ) ≤ ((n / 3 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h_lo_nonneg : (0 : ℝ) ≤ ((n : ℝ) - 2) / 3 := by linarith
    have hcube : (((n : ℝ) - 2) / 3) ^ 3 ≤ ((n / 3 : ℕ) : ℝ) ^ 3 :=
      pow_le_pow_left₀ h_lo_nonneg hq_lo 3
    have hsq : ((n / 3 : ℕ) : ℝ) ^ 2 ≤ ((n : ℝ) / 3) ^ 2 :=
      pow_le_pow_left₀ hq_nonneg hq_hi 2
    have h_q_bound : (5 / 2 : ℝ) * (((n : ℝ) - 2) / 3) ^ 3 - (3 / 2 : ℝ) * ((n : ℝ) / 3) ^ 2 ≤
        (((n / 3) ^ 3 + 3 * ((n / 3).choose 2 * (n / 3)) : ℕ) : ℝ) := by
      push_cast
      rw [choose_two_cast]
      have h_id2 : ((n / 3 : ℕ) : ℝ) ^ 3 +
          3 * (((n / 3 : ℕ) : ℝ) * (((n / 3 : ℕ) : ℝ) - 1) / 2 * ((n / 3 : ℕ) : ℝ)) =
          (5 / 2 : ℝ) * ((n / 3 : ℕ) : ℝ) ^ 3 - (3 / 2 : ℝ) * ((n / 3 : ℕ) : ℝ) ^ 2 := by ring
      rw [h_id2]
      linarith
    have h_comb : (((n / 3) ^ 3 + 3 * ((n / 3).choose 2 * (n / 3)) : ℕ) : ℝ) ≤
        (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := by
      exact_mod_cast (card_turanH_ge n).trans (turanH_le_extremal n)
    linarith
