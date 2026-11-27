import OMAReductions.R_RamseyNumbers_ramsey_number_three_six_R1

-- Step RamseyNumbers.ramsey_number_three_six.R1.H1: hypothesis H1 of reduction RamseyNumbers.ramsey_number_three_six.R1
-- Credit: @michielkosters
-- H1 := ∀ (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj], G.CliqueFree 3 →     (∀ v, G.degree v = 4 ∨ G.degree v = 5) → (∃ v, G.degree v = 4) → ¬ Gᶜ.CliqueFree 6  -- The remaining case is a 5-regular triangle-free graph.

open SimpleGraph

private lemma nonneighbors_four_regular
    (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6)
    (x : Fin 18) (hx : G.degree x = 4)
    (y : Fin 18) (hy : y ∈ Gᶜ.neighborFinset x) :
    (Gᶜ.neighborFinset x ∩ G.neighborFinset y).card = 4 := by
  classical
  have hcard : (Gᶜ.neighborFinset x).card = 13 := by
    rw [Gᶜ.card_neighborFinset_eq_degree, G.degree_compl, Fintype.card_fin, hx]
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 13) (s := Gᶜ.neighborFinset x) (by simp [hcard])
  have hsub_map : Finset.univ.map f ⊆ Gᶜ.neighborFinset x := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
    exact hf ⟨i, rfl⟩
  have hmap : Finset.univ.map f = Gᶜ.neighborFinset x :=
    Finset.eq_of_subset_of_card_le hsub_map (by simp [hcard])
  let H := G.comap f
  let e : H ↪g G := SimpleGraph.Embedding.comap f G
  let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
  have hH : H.CliqueFree 3 := CliqueFree.comap e.isContained hG
  have hHc : Hᶜ.CliqueFree 5 := by
    intro t ht
    have hs : Gᶜ.IsNClique 5 (t.map f) := by
      refine ⟨?_, (Finset.card_map _).trans ht.card_eq⟩
      intro u hu v hv huv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hv
      exact ec.map_adj_iff.mpr (ht.isClique hi hj (fun he => huv (congrArg f he)))
    apply hc _ (hs.insert (a := x) ?_)
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
    exact (Gᶜ.mem_neighborFinset x (f i)).mp (hf ⟨i, rfl⟩)
  have hdeg_all : ∀ i : Fin 13, H.degree i = 4 := by
    intro i
    have hlt := OMA.R_RamseyNumbers_ramsey_number_three_six_R1.degree_lt H hH hHc i
    have hnl := OMA.R_RamseyNumbers_ramsey_number_three_six_R1.nonneighbors_lt
      OMA.R_RamseyNumbers_ramsey_number_three_six_R1.nine_works H hH hHc i
    rw [H.degree_compl, Fintype.card_fin] at hnl
    omega
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp (hmap ▸ hy)
  have hinter : Gᶜ.neighborFinset x ∩ G.neighborFinset (f i) = (H.neighborFinset i).map f := by
    ext w
    simp only [← hmap, Finset.mem_inter, Finset.mem_map, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨⟨j, rfl⟩, hadj⟩
      exact ⟨j, hadj, rfl⟩
    · rintro ⟨j, hadj, rfl⟩
      exact ⟨⟨j, rfl⟩, hadj⟩
  rw [hinter, Finset.card_map, H.card_neighborFinset_eq_degree, hdeg_all i]

theorem OMA.solution : OMA.R_RamseyNumbers_ramsey_number_three_six_R1.H1 := by
  intro G _ hG hdeg ⟨v, hv⟩ hc
  let A := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  have hA_card : A.card = 4 := by
    rw [G.card_neighborFinset_eq_degree, hv]
  have hB_card : B.card = 13 := by
    rw [Gᶜ.card_neighborFinset_eq_degree, G.degree_compl, Fintype.card_fin, hv]
  have hAB_disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    rw [G.mem_neighborFinset] at hwA
    rw [Gᶜ.mem_neighborFinset] at hwB
    exact hwB.2 hwA
  have hA_indep : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y := by
    intro x hx y hy hxy
    have hind := G.isIndepSet_neighborSet_of_triangleFree hG v
    exact hind ((G.mem_neighborFinset v x).mp hx) ((G.mem_neighborFinset v y).mp hy)
      (G.ne_of_adj hxy) hxy
  have hA_deg_u : ∀ u ∈ B, (A ∩ G.neighborFinset u).card ≤ 1 := by
    intro u hu
    have hB_reg := nonneighbors_four_regular G hG hc v hv u hu
    have hsub : G.neighborFinset u ⊆ A ∪ B := by
      intro w hw
      rw [G.mem_neighborFinset] at hw
      have hvw : v ≠ w := by
        rintro rfl
        exact ((Gᶜ.mem_neighborFinset v u).mp hu).2 hw.symm
      by_cases hvw_adj : G.Adj v w
      · exact Finset.mem_union_left _ ((G.mem_neighborFinset v w).mpr hvw_adj)
      · exact Finset.mem_union_right _ ((Gᶜ.mem_neighborFinset v w).mpr ⟨hvw, hvw_adj⟩)
    have hsplit : G.neighborFinset u = (A ∩ G.neighborFinset u) ∪ (B ∩ G.neighborFinset u) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hw
        rcases Finset.mem_union.mp (hsub hw) with hA | hB
        · exact Or.inl ⟨hA, hw⟩
        · exact Or.inr ⟨hB, hw⟩
      · rintro (⟨_, hw⟩ | ⟨_, hw⟩) <;> exact hw
    have hdisj_u : Disjoint (A ∩ G.neighborFinset u) (B ∩ G.neighborFinset u) :=
      hAB_disj.mono Finset.inter_subset_left Finset.inter_subset_left
    have hdeg_u : G.degree u = (A ∩ G.neighborFinset u).card + (B ∩ G.neighborFinset u).card := by
      conv_lhs => rw [← G.card_neighborFinset_eq_degree, hsplit, Finset.card_union_of_disjoint hdisj_u]
    change (B ∩ G.neighborFinset u).card = 4 at hB_reg
    rcases hdeg u with h4 | h5 <;> omega
  have hsum_B : (∑ u ∈ B, (A ∩ G.neighborFinset u).card) ≤ 13 := by
    calc ∑ u ∈ B, (A ∩ G.neighborFinset u).card
      _ ≤ ∑ _u ∈ B, 1 := Finset.sum_le_sum hA_deg_u
      _ = 13 := by simp [hB_card]
  have hB_deg_a : ∀ a ∈ A, (B ∩ G.neighborFinset a).card + 1 = G.degree a := by
    intro a ha
    have hv_mem : v ∈ G.neighborFinset a :=
      (G.mem_neighborFinset a v).mpr ((G.mem_neighborFinset v a).mp ha).symm
    have heq : B ∩ G.neighborFinset a = (G.neighborFinset a).erase v := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_erase, Gᶜ.mem_neighborFinset,
        G.mem_neighborFinset, B]
      constructor
      · rintro ⟨⟨hvw, _⟩, haw⟩
        exact ⟨hvw.symm, haw⟩
      · rintro ⟨hwv, haw⟩
        refine ⟨⟨hwv.symm, ?_⟩, haw⟩
        intro hvw_adj
        exact hA_indep a ha w ((G.mem_neighborFinset v w).mpr hvw_adj) haw
    rw [heq, Finset.card_erase_add_one hv_mem, G.card_neighborFinset_eq_degree]
  have hsum_A : 15 ≤ ∑ x ∈ A, (B ∩ G.neighborFinset x).card := by
    by_cases h3 : ∃ a ∈ A, (B ∩ G.neighborFinset a).card = 3
    · rcases h3 with ⟨a, haA, ha3⟩
      have ha_deg : G.degree a = 4 := by
        have := hB_deg_a a haA
        omega
      have ha'_4 : ∀ a' ∈ A.erase a, (B ∩ G.neighborFinset a').card = 4 := by
        intro a' ha'
        have ha'A : a' ∈ A := Finset.mem_of_mem_erase ha'
        have hne : a ≠ a' := (Finset.ne_of_mem_erase ha').symm
        have ha'_mem : a' ∈ Gᶜ.neighborFinset a :=
          (Gᶜ.mem_neighborFinset a a').mpr ⟨hne, hA_indep a haA a' ha'A⟩
        have hreg := nonneighbors_four_regular G hG hc a ha_deg a' ha'_mem
        have hinter : Gᶜ.neighborFinset a ∩ G.neighborFinset a' = B ∩ G.neighborFinset a' := by
          ext w
          simp only [Finset.mem_inter, Gᶜ.mem_neighborFinset, G.mem_neighborFinset, B]
          constructor
          · rintro ⟨⟨_, haw⟩, ha'w⟩
            refine ⟨⟨?_, ?_⟩, ha'w⟩
            · rintro rfl
              exact haw ((G.mem_neighborFinset v a).mp haA).symm
            · intro hvw
              exact hA_indep a' ha'A w ((G.mem_neighborFinset v w).mpr hvw) ha'w
          · rintro ⟨hwB, ha'w⟩
            refine ⟨⟨?_, ?_⟩, ha'w⟩
            · rintro rfl
              exact Finset.disjoint_left.mp hAB_disj haA ((Gᶜ.mem_neighborFinset v a).mpr hwB)
            · intro haw
              have hsub2 : ({a, a'} : Finset (Fin 18)) ⊆ A ∩ G.neighborFinset w := by
                intro z hz
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with hza | hza'
                · rw [hza]
                  exact Finset.mem_inter.mpr ⟨haA, (G.mem_neighborFinset w a).mpr haw.symm⟩
                · rw [hza']
                  exact Finset.mem_inter.mpr ⟨ha'A, (G.mem_neighborFinset w a').mpr ha'w.symm⟩
              have hle := Finset.card_le_card hsub2
              rw [Finset.card_pair hne] at hle
              have hle1 := hA_deg_u w ((Gᶜ.mem_neighborFinset v w).mpr hwB)
              omega
        rw [← hinter, hreg]
      have hsplitA := Finset.add_sum_erase A (fun x => (B ∩ G.neighborFinset x).card) haA
      have hcard_erase : (A.erase a).card = 3 := by
        rw [Finset.card_erase_of_mem haA, hA_card]
      have hsum_erase : ∑ x ∈ A.erase a, (B ∩ G.neighborFinset x).card = 12 := by
        calc ∑ x ∈ A.erase a, (B ∩ G.neighborFinset x).card
          _ = ∑ _x ∈ A.erase a, 4 := Finset.sum_congr rfl ha'_4
          _ = 12 := by simp [hcard_erase]
      omega
    · have ha_4 : ∀ x ∈ A, (B ∩ G.neighborFinset x).card = 4 := by
        intro x hx
        have := hB_deg_a x hx
        rcases hdeg x with h4 | h5
        · exfalso; exact h3 ⟨x, hx, by omega⟩
        · omega
      calc 15 ≤ 16 := by omega
        _ = ∑ _x ∈ A, 4 := by simp [hA_card]
        _ = ∑ x ∈ A, (B ∩ G.neighborFinset x).card := (Finset.sum_congr rfl ha_4).symm
  have hdouble :
      ∑ x ∈ A, (B ∩ G.neighborFinset x).card = ∑ u ∈ B, (A ∩ G.neighborFinset u).card := by
    have hL : ∀ x, (B ∩ G.neighborFinset x).card = ∑ u ∈ B, if G.Adj x u then 1 else 0 := by
      intro x
      rw [← Finset.card_filter]
      congr 1
      ext u
      simp [G.mem_neighborFinset]
    have hR : ∀ u, (A ∩ G.neighborFinset u).card = ∑ x ∈ A, if G.Adj u x then 1 else 0 := by
      intro u
      rw [← Finset.card_filter]
      congr 1
      ext x
      simp [G.mem_neighborFinset]
    simp_rw [hL, hR]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun x _ => ?_
    simp [G.adj_comm]
  omega
