import OMAReductions.R_Arxiv_2107_00295_independentDominationOdd_R1

-- Step Arxiv.2107.00295.independentDominationOdd.R1.H1: hypothesis H1 of reduction Arxiv.2107.00295.independentDominationOdd.R1
-- Credit: @michielkosters
-- H1 := ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],     0 < G.minDegree → G.maxDegree ≤ 3 →     2 * G.indepDominationNumber ≤ Fintype.card V  /-- The connected case of Corollary 1.3 for an odd degree bound of at least five. -/

section Helpers

private lemma exists_indep_dominating_finset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ D : Finset V, G.IsIndepSet (D : Set V) ∧ G.IsDominating (D : Set V) := by
  let S : Finset (Finset V) :=
    Finset.univ.powerset.filter (fun D : Finset V => G.IsIndepSet (D : Set V))
  have hEmpty : (∅ : Finset V) ∈ S := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.empty_subset _, ?_⟩
    intro x hx
    simp at hx
  obtain ⟨D, hDS, hDmax⟩ := Finset.exists_max_image S Finset.card ⟨∅, hEmpty⟩
  have hDind : G.IsIndepSet (D : Set V) := (Finset.mem_filter.mp hDS).2
  refine ⟨D, hDind, ?_⟩
  intro v
  by_cases hv : v ∈ D
  · exact Or.inl hv
  · by_contra hno
    push Not at hno
    have hInsertInd : G.IsIndepSet ((insert v D : Finset V) : Set V) := by
      intro x hx y hy hxy hadj
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact hxy rfl
      · exact hno.2 y hy hadj
      · exact hno.2 x hx hadj.symm
      · exact hDind hx hy hxy hadj
    have hInsertS : insert v D ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hInsertInd⟩
    have hle := hDmax (insert v D) hInsertS
    have hcard : (insert v D).card = D.card + 1 := by simp [hv]
    omega

private lemma exists_indep_dom_min {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ D : Finset V, G.IsNIndepDominatingSet G.indepDominationNumber D := by
  obtain ⟨D0, hI, hD⟩ := exists_indep_dominating_finset G
  have hne : {n | ∃ D : Finset V, G.IsNIndepDominatingSet n D}.Nonempty :=
    ⟨D0.card, D0, hI, hD, rfl⟩
  exact Nat.sInf_mem hne

private lemma indepDominationNumber_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {D : Finset V}
    (hI : G.IsIndepSet (D : Set V)) (hDom : G.IsDominating (D : Set V)) :
    G.indepDominationNumber ≤ D.card :=
  Nat.sInf_le ⟨D, hI, hDom, rfl⟩

private def isoAfterN [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V :=
  Finset.univ.filter (fun w =>
    w ∉ insert u (G.neighborFinset u) ∧
    G.neighborFinset w ⊆ insert u (G.neighborFinset u))

private lemma mem_isoAfterN {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u w : V} :
    w ∈ isoAfterN G u ↔
      w ∉ insert u (G.neighborFinset u) ∧
      G.neighborFinset w ⊆ insert u (G.neighborFinset u) := by
  simp [isoAfterN]

private lemma neighborFinset_subset_of_mem_isoAfterN {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u w : V} (hw : w ∈ isoAfterN G u) :
    G.neighborFinset w ⊆ G.neighborFinset u := by
  rw [mem_isoAfterN] at hw
  intro x hx
  have hx1 := hw.2 hx
  rcases Finset.mem_insert.mp hx1 with hxu | hx2
  · rw [hxu, SimpleGraph.mem_neighborFinset] at hx
    exact False.elim (hw.1 (Finset.mem_insert_of_mem ((G.mem_neighborFinset u w).mpr hx.symm)))
  · exact hx2

private lemma exists_good_vertex {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hmin : 0 < G.minDegree) (hmax : G.maxDegree ≤ 3) :
    ∃ u : V, (isoAfterN G u).card + 1 ≤ G.degree u := by
  have hdeg_pos : ∀ x : V, 0 < G.degree x := fun x =>
    lt_of_lt_of_le hmin (G.minDegree_le_degree x)
  have hdeg_le : ∀ x : V, G.degree x ≤ 3 := fun x =>
    (G.degree_le_maxDegree x).trans hmax
  by_cases h1 : ∃ u : V, G.degree u = 1
  · rcases h1 with ⟨u, hdu⟩
    have hcard_u : (G.neighborFinset u).card = 1 := by
      simpa only [SimpleGraph.degree] using hdu
    obtain ⟨v, hNu⟩ := Finset.card_eq_one.mp hcard_u
    by_cases hv : (isoAfterN G v).card + 1 ≤ G.degree v
    · exact ⟨v, hv⟩
    · have hv_lt : G.degree v ≤ (isoAfterN G v).card := by omega
      have huv : u ∈ G.neighborFinset v := by
        rw [SimpleGraph.mem_neighborFinset]
        exact ((G.mem_neighborFinset u v).mp (by rw [hNu]; simp)).symm
      let S : Finset V := (G.neighborFinset v).erase u
      have hScard : S.card = G.degree v - 1 := by
        simp only [S, SimpleGraph.degree]
        exact Finset.card_erase_of_mem huv
      have hcov : isoAfterN G v ⊆
          S.biUnion (fun s => (isoAfterN G v).filter (fun w => G.Adj s w)) := by
        intro w hw
        have hwN : G.neighborFinset w ⊆ G.neighborFinset v :=
          neighborFinset_subset_of_mem_isoAfterN G hw
        have hposw : 0 < (G.neighborFinset w).card := by
          simpa only [SimpleGraph.degree] using hdeg_pos w
        obtain ⟨s, hs⟩ := Finset.card_pos.mp hposw
        have hsv : s ∈ G.neighborFinset v := hwN hs
        have hsu : s ≠ u := by
          intro hsu
          rw [hsu] at hs
          have hwu : w ∈ G.neighborFinset u :=
            (G.mem_neighborFinset u w).mpr ((G.mem_neighborFinset w u).mp hs).symm
          rw [hNu, Finset.mem_singleton] at hwu
          rw [hwu] at hw
          exact ((mem_isoAfterN G).mp hw).1 (Finset.mem_insert_self v _)
        refine Finset.mem_biUnion.mpr ⟨s, Finset.mem_erase.mpr ⟨hsu, hsv⟩, ?_⟩
        exact Finset.mem_filter.mpr ⟨hw, ((G.mem_neighborFinset w s).mp hs).symm⟩
      have hex : ∃ s ∈ S, 2 ≤ ((isoAfterN G v).filter (fun w => G.Adj s w)).card := by
        by_contra hno
        push Not at hno
        have h1' : (isoAfterN G v).card ≤
            (S.biUnion (fun s => (isoAfterN G v).filter (fun w => G.Adj s w))).card :=
          Finset.card_le_card hcov
        have h2' : (S.biUnion (fun s => (isoAfterN G v).filter (fun w => G.Adj s w))).card ≤
            ∑ s ∈ S, ((isoAfterN G v).filter (fun w => G.Adj s w)).card :=
          Finset.card_biUnion_le
        have h3' : ∑ s ∈ S, ((isoAfterN G v).filter (fun w => G.Adj s w)).card ≤ ∑ _s ∈ S, 1 :=
          Finset.sum_le_sum (fun s hs => Nat.le_of_lt_succ (hno s hs))
        have h4' : (∑ _s ∈ S, (1 : ℕ)) = S.card := by simp
        have hdv_pos := hdeg_pos v
        omega
      rcases hex with ⟨s, hsS, hsF⟩
      let F : Finset V := (isoAfterN G v).filter (fun w => G.Adj s w)
      have hsF' : 2 ≤ F.card := hsF
      have hv_not_F : v ∉ F := by
        intro hvF
        exact ((mem_isoAfterN G).mp (Finset.mem_filter.mp hvF).1).1 (Finset.mem_insert_self v _)
      have hsub_s : insert v F ⊆ G.neighborFinset s := by
        intro x hx
        rcases Finset.mem_insert.mp hx with hxv | hxF
        · rw [hxv, SimpleGraph.mem_neighborFinset]
          exact ((G.mem_neighborFinset v s).mp (Finset.mem_erase.mp hsS).2).symm
        · rw [SimpleGraph.mem_neighborFinset]
          exact (Finset.mem_filter.mp hxF).2
      have hcard_ins : (insert v F).card = F.card + 1 := by simp [hv_not_F]
      have hcard_s : (G.neighborFinset s).card ≤ 3 := by
        simpa only [SimpleGraph.degree] using hdeg_le s
      have hcard_ins_le : (insert v F).card ≤ (G.neighborFinset s).card :=
        Finset.card_le_card hsub_s
      have hNs_eq : G.neighborFinset s = insert v F :=
        (Finset.eq_of_subset_of_card_le hsub_s (by omega)).symm
      have hdeg_s : G.degree s = 3 := by
        have hcs3 : (G.neighborFinset s).card = 3 := by omega
        simpa only [SimpleGraph.degree] using hcs3
      have hWs_sub : isoAfterN G s ⊆ (G.neighborFinset v).erase s := by
        intro z hz
        have hzN : G.neighborFinset z ⊆ G.neighborFinset s :=
          neighborFinset_subset_of_mem_isoAfterN G hz
        have hposz : 0 < (G.neighborFinset z).card := by
          simpa only [SimpleGraph.degree] using hdeg_pos z
        obtain ⟨x, hx⟩ := Finset.card_pos.mp hposz
        have hxs : x ∈ insert v F := hNs_eq ▸ hzN hx
        have hzv : z ∈ G.neighborFinset v := by
          rcases Finset.mem_insert.mp hxs with hxv | hxF
          · rw [hxv] at hx
            exact (G.mem_neighborFinset v z).mpr ((G.mem_neighborFinset z v).mp hx).symm
          · have hxW : x ∈ isoAfterN G v := (Finset.mem_filter.mp hxF).1
            exact neighborFinset_subset_of_mem_isoAfterN G hxW
              ((G.mem_neighborFinset x z).mpr ((G.mem_neighborFinset z x).mp hx).symm)
        have hzs : z ≠ s := by
          intro hzs
          rw [hzs] at hz
          exact ((mem_isoAfterN G).mp hz).1 (Finset.mem_insert_self s _)
        exact Finset.mem_erase.mpr ⟨hzs, hzv⟩
      have hsv' : s ∈ G.neighborFinset v := (Finset.mem_erase.mp hsS).2
      have hWs_card : (isoAfterN G s).card ≤ 2 := by
        have h1' := Finset.card_le_card hWs_sub
        have h2' : ((G.neighborFinset v).erase s).card = G.degree v - 1 := by
          simpa only [SimpleGraph.degree] using Finset.card_erase_of_mem hsv'
        have hdv_le := hdeg_le v
        omega
      exact ⟨s, by omega⟩
  · have hdeg_ge2 : ∀ x : V, 2 ≤ G.degree x := by
      intro x
      have hx1 := hdeg_pos x
      have hxne : G.degree x ≠ 1 := fun h => h1 ⟨x, h⟩
      omega
    by_cases h2 : ∃ u : V, G.degree u = 2
    · rcases h2 with ⟨u, hdu⟩
      by_cases hu : (isoAfterN G u).card + 1 ≤ G.degree u
      · exact ⟨u, hu⟩
      · have hu_ge : 2 ≤ (isoAfterN G u).card := by omega
        have hpos_u : 0 < (G.neighborFinset u).card := by
          simpa only [SimpleGraph.degree] using hdeg_pos u
        obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos_u
        have hw_eq : ∀ w ∈ isoAfterN G u, G.neighborFinset w = G.neighborFinset u := by
          intro w hw
          have hsub := neighborFinset_subset_of_mem_isoAfterN G hw
          have hcw : 2 ≤ (G.neighborFinset w).card := by
            simpa only [SimpleGraph.degree] using hdeg_ge2 w
          have hcu : (G.neighborFinset u).card = 2 := by
            simpa only [SimpleGraph.degree] using hdu
          exact Finset.eq_of_subset_of_card_le hsub (by omega)
        have hu_not_W : u ∉ isoAfterN G u := fun h =>
          ((mem_isoAfterN G).mp h).1 (Finset.mem_insert_self u _)
        have hsub_a : insert u (isoAfterN G u) ⊆ G.neighborFinset a := by
          intro x hx
          rcases Finset.mem_insert.mp hx with hxu | hxW
          · rw [hxu]
            exact (G.mem_neighborFinset a u).mpr ((G.mem_neighborFinset u a).mp ha).symm
          · have ha_w : a ∈ G.neighborFinset x := (hw_eq x hxW).symm ▸ ha
            exact (G.mem_neighborFinset a x).mpr ((G.mem_neighborFinset x a).mp ha_w).symm
        have hcard_ins : (insert u (isoAfterN G u)).card = (isoAfterN G u).card + 1 := by
          simp [hu_not_W]
        have hcard_a_le : (G.neighborFinset a).card ≤ 3 := by
          simpa only [SimpleGraph.degree] using hdeg_le a
        have hcard_ins_le : (insert u (isoAfterN G u)).card ≤ (G.neighborFinset a).card :=
          Finset.card_le_card hsub_a
        have hNa_eq : G.neighborFinset a = insert u (isoAfterN G u) :=
          (Finset.eq_of_subset_of_card_le hsub_a (by omega)).symm
        have hdeg_a : G.degree a = 3 := by
          have hca3 : (G.neighborFinset a).card = 3 := by omega
          simpa only [SimpleGraph.degree] using hca3
        have hWa_sub : isoAfterN G a ⊆ (G.neighborFinset u).erase a := by
          intro z hz
          have hzN : G.neighborFinset z ⊆ G.neighborFinset a :=
            neighborFinset_subset_of_mem_isoAfterN G hz
          have hposz : 0 < (G.neighborFinset z).card := by
            simpa only [SimpleGraph.degree] using hdeg_pos z
          obtain ⟨x, hx⟩ := Finset.card_pos.mp hposz
          have hxa : x ∈ insert u (isoAfterN G u) := hNa_eq ▸ hzN hx
          have hzx : z ∈ G.neighborFinset x :=
            (G.mem_neighborFinset x z).mpr ((G.mem_neighborFinset z x).mp hx).symm
          have hzu : z ∈ G.neighborFinset u := by
            rcases Finset.mem_insert.mp hxa with hxu | hxW
            · rw [hxu] at hzx; exact hzx
            · exact (hw_eq x hxW) ▸ hzx
          have hza : z ≠ a := by
            intro hza
            rw [hza] at hz
            exact ((mem_isoAfterN G).mp hz).1 (Finset.mem_insert_self a _)
          exact Finset.mem_erase.mpr ⟨hza, hzu⟩
        have hWa_card : (isoAfterN G a).card ≤ 1 := by
          have h1' := Finset.card_le_card hWa_sub
          have h2' : ((G.neighborFinset u).erase a).card = G.degree u - 1 := by
            simpa only [SimpleGraph.degree] using Finset.card_erase_of_mem ha
          omega
        exact ⟨a, by omega⟩
    · have hdeg3 : ∀ x : V, G.degree x = 3 := by
        intro x
        have hx2 := hdeg_ge2 x
        have hx3 := hdeg_le x
        have hxne : G.degree x ≠ 2 := fun h => h2 ⟨x, h⟩
        omega
      obtain ⟨u⟩ := ‹Nonempty V›
      have hpos_u : 0 < (G.neighborFinset u).card := by
        simpa only [SimpleGraph.degree] using hdeg_pos u
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos_u
      have hw_eq : ∀ w ∈ isoAfterN G u, G.neighborFinset w = G.neighborFinset u := by
        intro w hw
        have hsub := neighborFinset_subset_of_mem_isoAfterN G hw
        have hcw : (G.neighborFinset w).card = 3 := by
          simpa only [SimpleGraph.degree] using hdeg3 w
        have hcu : (G.neighborFinset u).card = 3 := by
          simpa only [SimpleGraph.degree] using hdeg3 u
        exact Finset.eq_of_subset_of_card_le hsub (by omega)
      have hu_not_W : u ∉ isoAfterN G u := fun h =>
        ((mem_isoAfterN G).mp h).1 (Finset.mem_insert_self u _)
      have hsub_a : insert u (isoAfterN G u) ⊆ G.neighborFinset a := by
        intro x hx
        rcases Finset.mem_insert.mp hx with hxu | hxW
        · rw [hxu]
          exact (G.mem_neighborFinset a u).mpr ((G.mem_neighborFinset u a).mp ha).symm
        · have ha_w : a ∈ G.neighborFinset x := (hw_eq x hxW).symm ▸ ha
          exact (G.mem_neighborFinset a x).mpr ((G.mem_neighborFinset x a).mp ha_w).symm
      have hcard_ins : (insert u (isoAfterN G u)).card = (isoAfterN G u).card + 1 := by
        simp [hu_not_W]
      have hcard_ins_le : (insert u (isoAfterN G u)).card ≤ (G.neighborFinset a).card :=
        Finset.card_le_card hsub_a
      have hca : (G.neighborFinset a).card = 3 := by
        simpa only [SimpleGraph.degree] using hdeg3 a
      have hdu3 := hdeg3 u
      exact ⟨u, by omega⟩

private lemma h1_induce_min_max {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hmax : G.maxDegree ≤ 3) (u : V)
    (R : Finset V) (hR : R = Finset.univ \ (insert u (G.neighborFinset u) ∪ isoAfterN G u))
    (hRne : R.Nonempty) [DecidableRel (G.induce (R : Set V)).Adj] :
    0 < (G.induce (R : Set V)).minDegree ∧ (G.induce (R : Set V)).maxDegree ≤ 3 := by
  let Ncl : Finset V := insert u (G.neighborFinset u)
  let W : Finset V := isoAfterN G u
  let Rtype : Type := {x : V // x ∈ (R : Set V)}
  let G' : SimpleGraph Rtype := G.induce (R : Set V)
  have : Nonempty Rtype := let ⟨r, hr⟩ := hRne; ⟨⟨r, hr⟩⟩
  refine ⟨?_, ?_⟩
  · refine Nat.succ_le_of_lt (lt_of_lt_of_le Nat.zero_lt_one ?_)
    refine G'.le_minDegree_of_forall_le_degree 1 ?_
    intro v
    have hvR : v.1 ∈ Finset.univ \ (Ncl ∪ W) := (Finset.ext_iff.mp hR v.1).mp v.2
    have hv_not_NW : v.1 ∉ Ncl ∪ W := (Finset.mem_sdiff.mp hvR).2
    have hv_not_N : v.1 ∉ Ncl := fun h => hv_not_NW (Finset.mem_union_left W h)
    have hv_not_W : v.1 ∉ W := fun h => hv_not_NW (Finset.mem_union_right Ncl h)
    have hnot_sub : ¬ G.neighborFinset v.1 ⊆ Ncl := by
      intro hsub
      exact hv_not_W ((mem_isoAfterN G).mpr ⟨hv_not_N, hsub⟩)
    rw [Finset.not_subset] at hnot_sub
    rcases hnot_sub with ⟨y, hyN, hy_not_N⟩
    have hy_not_W : y ∉ W := by
      intro hyW
      have hvN : v.1 ∈ Ncl := Finset.mem_insert_of_mem
        (neighborFinset_subset_of_mem_isoAfterN G hyW
          ((G.mem_neighborFinset y v.1).mpr ((G.mem_neighborFinset v.1 y).mp hyN).symm))
      exact hv_not_N hvN
    have hyR : y ∈ R := by
      rw [hR]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, by
        rw [Finset.mem_union]
        rintro (h | h) <;> contradiction⟩
    have hy_nbr : (⟨y, hyR⟩ : Rtype) ∈ G'.neighborFinset v := by
      rw [SimpleGraph.mem_neighborFinset]
      exact (G.mem_neighborFinset v.1 y).mp hyN
    have hpos' : 1 ≤ (G'.neighborFinset v).card :=
      Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨⟨y, hyR⟩, hy_nbr⟩)
    simpa only [SimpleGraph.degree] using hpos'
  · refine G'.maxDegree_le_of_forall_degree_le 3 ?_
    intro v
    have hsub : (G'.neighborFinset v).map ⟨Subtype.val, Subtype.val_injective⟩ ⊆
        G.neighborFinset v.1 := by
      intro x hx
      rcases Finset.mem_map.mp hx with ⟨w, hw, rfl⟩
      rw [SimpleGraph.mem_neighborFinset] at hw ⊢
      exact hw
    calc G'.degree v = (G'.neighborFinset v).card := by simp only [SimpleGraph.degree]
      _ = ((G'.neighborFinset v).map ⟨Subtype.val, Subtype.val_injective⟩).card :=
          (Finset.card_map _).symm
      _ ≤ (G.neighborFinset v.1).card := Finset.card_le_card hsub
      _ = G.degree v.1 := by simp only [SimpleGraph.degree]
      _ ≤ G.maxDegree := G.degree_le_maxDegree v.1
      _ ≤ 3 := hmax

private lemma h1_strong :
    ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → 0 < G.minDegree → G.maxDegree ≤ 3 →
      2 * G.indepDominationNumber ≤ Fintype.card V := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G _ hcard hmin hmax
    by_cases hzero : n = 0
    · subst hzero
      have hle : G.indepDominationNumber ≤ (∅ : Finset V).card := by
        refine indepDominationNumber_le_card G ?_ ?_
        · intro x hx
          simp at hx
        · intro v
          have hv : Fintype.card V = 0 := hcard
          exact False.elim ((Fintype.card_eq_zero_iff.mp hv).elim v)
      simp at hle
      omega
    · have hpos_card : 0 < Fintype.card V := by omega
      have : Nonempty V := Fintype.card_pos_iff.mp hpos_card
      obtain ⟨u, hu⟩ := exists_good_vertex G hmin hmax
      let Ncl : Finset V := insert u (G.neighborFinset u)
      let W : Finset V := isoAfterN G u
      let R : Finset V := Finset.univ \ (Ncl ∪ W)
      have hu' : W.card + 1 ≤ G.degree u := hu
      have huN : u ∉ G.neighborFinset u := fun h =>
        G.ne_of_adj ((G.mem_neighborFinset u u).mp h) rfl
      have hNcl_card : Ncl.card = G.degree u + 1 := by
        have h1' : (insert u (G.neighborFinset u)).card = (G.neighborFinset u).card + 1 := by
          simp [huN]
        have h2' : (G.neighborFinset u).card = G.degree u := by
          simp only [SimpleGraph.degree]
        exact h1'.trans (congrArg (· + 1) h2')
      have hdisj_NW : Disjoint Ncl W := by
        rw [Finset.disjoint_left]
        intro x hxN hxW
        exact ((mem_isoAfterN G).mp hxW).1 hxN
      have hdisj_NWR : Disjoint (Ncl ∪ W) R := disjoint_sdiff_self_right
      have hunion : (Ncl ∪ W) ∪ R = Finset.univ :=
        Finset.union_sdiff_of_subset (Finset.subset_univ _)
      have hV_card : Ncl.card + W.card + R.card = Fintype.card V := by
        rw [← Finset.card_union_of_disjoint hdisj_NW, ← Finset.card_union_of_disjoint hdisj_NWR,
          hunion, Finset.card_univ]
      have hW_ind : G.IsIndepSet ((insert u W : Finset V) : Set V) := by
        intro x hx y hy hxy hadj
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
        rcases hx with rfl | hxW <;> rcases hy with rfl | hyW
        · exact hxy rfl
        · exact ((mem_isoAfterN G).mp hyW).1
            (Finset.mem_insert_of_mem ((G.mem_neighborFinset x y).mpr hadj))
        · exact ((mem_isoAfterN G).mp hxW).1
            (Finset.mem_insert_of_mem ((G.mem_neighborFinset y x).mpr hadj.symm))
        · have hyN := neighborFinset_subset_of_mem_isoAfterN G hxW
            ((G.mem_neighborFinset x y).mpr hadj)
          exact ((mem_isoAfterN G).mp hyW).1 (Finset.mem_insert_of_mem hyN)
      have hu_not_W : u ∉ W := fun h =>
        ((mem_isoAfterN G).mp h).1 (Finset.mem_insert_self u _)
      have hInsW_card : (insert u W).card = W.card + 1 := by simp [hu_not_W]
      by_cases hRempty : R = ∅
      · have hR0 : R.card = 0 := by rw [hRempty]; simp
        have hDom : G.IsDominating ((insert u W : Finset V) : Set V) := by
          intro v
          by_cases hvN : v ∈ Ncl
          · rcases Finset.mem_insert.mp hvN with rfl | hvNu
            · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_insert_self v _))
            · exact Or.inr ⟨u, Finset.mem_coe.mpr (Finset.mem_insert_self u _),
                ((G.mem_neighborFinset u v).mp hvNu).symm⟩
          · have hvU : v ∈ (Ncl ∪ W) ∪ R := hunion ▸ Finset.mem_univ v
            rw [hRempty, Finset.union_empty, Finset.mem_union] at hvU
            rcases hvU with h1' | hvW
            · exact False.elim (hvN h1')
            · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hvW))
        have hle := indepDominationNumber_le_card G hW_ind hDom
        omega
      · have hRne : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr hRempty
        let Rtype : Type := {x : V // x ∈ (R : Set V)}
        let G' : SimpleGraph Rtype := G.induce (R : Set V)
        let : DecidableRel G'.Adj := fun a b => ‹DecidableRel G.Adj› a.1 b.1
        have hRcard_eq : Fintype.card Rtype = R.card := by simp [Rtype]
        have hR_lt : R.card < n := by omega
        obtain ⟨hmin', hmax'⟩ := @h1_induce_min_max V _ _ G _ hmax u R rfl hRne
          (fun a b => ‹DecidableRel G.Adj› a.1 b.1)
        have hmin'' : 0 < G'.minDegree := by convert hmin'
        have hmax'' : G'.maxDegree ≤ 3 := by convert hmax'
        have hIH := ih R.card hR_lt Rtype G' hRcard_eq hmin'' hmax''
        obtain ⟨D', hD'⟩ := exists_indep_dom_min G'
        let DR : Finset V := D'.map ⟨Subtype.val, Subtype.val_injective⟩
        let D : Finset V := insert u W ∪ DR
        have hDR_sub : DR ⊆ R := by
          intro x hx
          rcases Finset.mem_map.mp hx with ⟨y, _, rfl⟩
          exact y.2
        have hdisj_WDR : Disjoint (insert u W) DR := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          have hxR := hDR_sub hx2
          have hx_not_NW := (Finset.mem_sdiff.mp hxR).2
          rcases Finset.mem_insert.mp hx1 with rfl | hxW
          · exact hx_not_NW (Finset.mem_union_left W (Finset.mem_insert_self x _))
          · exact hx_not_NW (Finset.mem_union_right Ncl hxW)
        have hD_ind : G.IsIndepSet (D : Set V) := by
          intro x hx y hy hxy hadj
          simp only [D, Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx hy
          rcases hx with hx1 | hx2 <;> rcases hy with hy1 | hy2
          · exact hW_ind hx1 hy1 hxy hadj
          · have hyR := hDR_sub hy2
            have hy_not_N : y ∉ Ncl := fun h =>
              (Finset.mem_sdiff.mp hyR).2 (Finset.mem_union_left W h)
            rcases Finset.mem_insert.mp hx1 with rfl | hxW
            · exact hy_not_N (Finset.mem_insert_of_mem ((G.mem_neighborFinset x y).mpr hadj))
            · have hyN := neighborFinset_subset_of_mem_isoAfterN G hxW
                ((G.mem_neighborFinset x y).mpr hadj)
              exact hy_not_N (Finset.mem_insert_of_mem hyN)
          · have hxR := hDR_sub hx2
            have hx_not_N : x ∉ Ncl := fun h =>
              (Finset.mem_sdiff.mp hxR).2 (Finset.mem_union_left W h)
            rcases Finset.mem_insert.mp hy1 with rfl | hyW
            · exact hx_not_N (Finset.mem_insert_of_mem ((G.mem_neighborFinset y x).mpr hadj.symm))
            · have hxN := neighborFinset_subset_of_mem_isoAfterN G hyW
                ((G.mem_neighborFinset y x).mpr hadj.symm)
              exact hx_not_N (Finset.mem_insert_of_mem hxN)
          · rcases Finset.mem_map.mp hx2 with ⟨a, ha, rfl⟩
            rcases Finset.mem_map.mp hy2 with ⟨b, hb, rfl⟩
            exact hD'.isIndep ha hb (fun h => hxy (congrArg Subtype.val h)) hadj
        have hD_dom : G.IsDominating (D : Set V) := by
          intro v
          by_cases hvN : v ∈ Ncl
          · rcases Finset.mem_insert.mp hvN with rfl | hvNu
            · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_union_left DR (Finset.mem_insert_self v _)))
            · exact Or.inr ⟨u, Finset.mem_coe.mpr (Finset.mem_union_left DR (Finset.mem_insert_self u _)),
                ((G.mem_neighborFinset u v).mp hvNu).symm⟩
          · by_cases hvW : v ∈ W
            · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_union_left DR (Finset.mem_insert_of_mem hvW)))
            · have hvR : v ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, by
                rw [Finset.mem_union]
                rintro (h | h) <;> contradiction⟩
              rcases hD'.isDominating ⟨v, hvR⟩ with h1' | ⟨w, hw, hvw⟩
              · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_union_right (insert u W)
                  (Finset.mem_map.mpr ⟨⟨v, hvR⟩, h1', rfl⟩)))
              · exact Or.inr ⟨w.1, Finset.mem_coe.mpr (Finset.mem_union_right (insert u W)
                  (Finset.mem_map.mpr ⟨w, hw, rfl⟩)), hvw⟩
        have hD_card : D.card = W.card + 1 + G'.indepDominationNumber := by
          rw [Finset.card_union_of_disjoint hdisj_WDR, hInsW_card]
          have hDR_card : DR.card = D'.card := Finset.card_map _
          rw [hDR_card, hD'.card_eq]
        have hle := indepDominationNumber_le_card G hD_ind hD_dom
        omega

end Helpers

theorem OMA.solution : OMA.R_Arxiv_2107_00295_independentDominationOdd_R1.H1 := by
  intro V _ _ G _ hmin hmax
  exact h1_strong (Fintype.card V) V G rfl hmin hmax
