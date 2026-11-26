import FormalConjectures.ErdosProblems.«652»

/-! A distance pair from two distinct centers has at most two preimages. -/

open scoped EuclideanGeometry

theorem OMA.solution : type_of% @Erdos652.erdos_652.variants.product := by
  classical
  let : DecidableEq ℝ² := Classical.decEq _
  let : DecidableEq ℝ := Classical.decEq _
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro points p hp q hq hpq
  let remaining := (points.erase p).erase q
  let pDistances := (points.erase p).image (fun x => dist x p)
  let qDistances := (points.erase q).image (fun x => dist x q)
  let distancePair (x : ℝ²) : ℝ × ℝ := (dist x p, dist x q)
  have hp' : p ∈ points.erase q := Finset.mem_erase.mpr ⟨hpq, hp⟩
  have hq' : q ∈ points.erase p := Finset.mem_erase.mpr ⟨hpq.symm, hq⟩
  have hremaining : remaining.card = points.card - 1 - 1 := by
    dsimp [remaining]
    rw [Finset.card_erase_of_mem hq', Finset.card_erase_of_mem hp]
  have hmaps : ∀ x ∈ remaining, distancePair x ∈ pDistances ×ˢ qDistances := by
    intro x hx
    obtain ⟨hxq, hxp⟩ := Finset.mem_erase.mp hx
    have hx' : x ∈ points.erase q :=
      Finset.mem_erase.mpr ⟨hxq, (Finset.mem_erase.mp hxp).2⟩
    exact Finset.mk_mem_product (Finset.mem_image_of_mem _ hxp) (Finset.mem_image_of_mem _ hx')
  have hfiber : ∀ d ∈ pDistances ×ˢ qDistances,
      (remaining.filter fun x => distancePair x = d).card ≤ 2 := by
    intro d _
    let fiber := remaining.filter fun x => distancePair x = d
    change fiber.card ≤ 2
    by_cases hsmall : fiber.card ≤ 1
    · omega
    · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < fiber.card)
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have hdim : Module.finrank ℝ ℝ² = 2 := finrank_euclideanSpace_fin
      calc
        fiber.card ≤ ({a, b} : Finset ℝ²).card := by
          apply Finset.card_le_card
          intro x hx
          have hx' := (Finset.mem_filter.mp hx).2
          obtain h | h := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
            hdim hpq hab (congrArg Prod.fst ha') (congrArg Prod.fst hb') (congrArg Prod.fst hx')
            (congrArg Prod.snd ha') (congrArg Prod.snd hb') (congrArg Prod.snd hx')
          · simp [h]
          · simp [h]
        _ ≤ 2 := Finset.card_le_two
  have hcount := Finset.card_le_mul_card_image_of_maps_to hmaps 2 hfiber
  rw [Finset.card_product, hremaining] at hcount
  have hn : 1 < points.card := Finset.one_lt_card.mpr ⟨p, hp, q, hq, hpq⟩
  have hDp : 0 < pDistances.card :=
    Finset.card_pos.mpr ⟨dist q p, Finset.mem_image_of_mem _ hq'⟩
  have hDq : 0 < qDistances.card :=
    Finset.card_pos.mpr ⟨dist p q, Finset.mem_image_of_mem _ hp'⟩
  have hpos := Nat.mul_pos hDp hDq
  have hbound : points.card ≤ 4 * (pDistances.card * qDistances.card) := by omega
  have hboundR : (points.card : ℝ) ≤ 4 * ((pDistances.card : ℝ) * (qDistances.card : ℝ)) := by
    exact_mod_cast hbound
  change (1 / 4 : ℝ) * (points.card : ℝ) ≤ (pDistances.card : ℝ) * (qDistances.card : ℝ)
  linarith