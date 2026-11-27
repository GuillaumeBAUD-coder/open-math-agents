import OMAReductions.R_Arxiv_2107_00295_independentDominationEven_R1

/-!
# Independent domination in graphs of maximum degree two

If a minimum independent dominating set is larger than its complement, take
a smallest subset with fewer neighbours than vertices. Every neighbour has
two neighbours in that subset by minimality. The degree bound then forces
all its neighbours to lie there. Exchanging the subset for its neighbourhood
keeps the set independent and dominating and decreases its size.
-/

namespace OMA.IndependentDominationTwo

open Finset SimpleGraph

private theorem exists_optimal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    ∃ S : Finset V, G.IsNIndepDominatingSet G.indepDominationNumber S := by
  classical
  obtain ⟨S, hS⟩ := G.maximumIndepSet_exists
  have hdom : G.IsDominating S := by
    intro v
    by_cases hv : v ∈ S
    · exact Or.inl hv
    · right
      by_contra hd
      have hins : G.IsIndepSet (insert v (S : Set V)) := by
        apply Set.Pairwise.insert_of_notMem hv hS.isIndepSet
        intro w hw
        exact ⟨fun h => hd ⟨w, hw, h⟩, fun h => hd ⟨w, hw, h.symm⟩⟩
      exact hv ((hS.isMaximalIndepSet S).2 hins (Set.subset_insert _ _) (Set.mem_insert _ _))
  have he : {n | ∃ T : Finset V, G.IsNIndepDominatingSet n T}.Nonempty :=
    ⟨S.card, S, hS.isIndepSet, hdom, rfl⟩
  exact Nat.sInf_mem he

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : 0 < G.minDegree) (hmax : G.maxDegree ≤ 2) :
    2 * G.indepDominationNumber ≤ Fintype.card V := by
  classical
  obtain ⟨S, hS⟩ := exists_optimal G
  rw [← hS.card_eq]
  by_contra! hTooLarge
  let N (R : Finset V) := univ.filter fun v => ∃ x ∈ R, G.Adj v x
  have hN {v : V} {R : Finset V} : v ∈ N R ↔ ∃ x ∈ R, G.Adj v x := by
    simp [N]
  have hDisjoint {R : Finset V} (hRS : R ⊆ S) {v : V} (hv : v ∈ N R) : v ∉ S := by
    intro hvS
    obtain ⟨x, hx, hAdj⟩ := hN.mp hv
    exact hS.isIndep hvS (hRS hx) hAdj.ne hAdj
  have hsub : N S ⊆ Sᶜ := fun v hv => mem_compl.mpr (hDisjoint Subset.rfl hv)
  have hDefect : (N S).card < S.card := by
    have hC := card_le_card hsub
    rw [card_compl] at hC
    have hs := card_le_univ S
    omega
  let P (k : ℕ) := ∃ R : Finset V, R ⊆ S ∧ R.card = k ∧ (N R).card < R.card
  have hP : ∃ k, P k := ⟨S.card, S, Subset.rfl, rfl, hDefect⟩
  obtain ⟨R, hRS, hRcard, hRdef⟩ := Nat.find_spec hP
  have hFull {v : V} (hv : v ∈ N R) {z : V} (hAdj : G.Adj v z) : z ∈ R := by
    obtain ⟨x, hx, hAx⟩ := hN.mp hv
    have hTwo : ∃ y ∈ R, y ≠ x ∧ G.Adj v y := by
      by_contra! hMissing
      let R' := R.erase x
      have hVs : N R' ⊆ (N R).erase v := by
        intro w hw
        obtain ⟨y, hy, hAy⟩ := hN.mp hw
        obtain ⟨hyx, hyR⟩ := mem_erase.mp hy
        have hwv : w ≠ v := by
          intro he
          subst w
          exact hMissing y hyR hyx hAy
        exact mem_erase.mpr ⟨hwv, hN.mpr ⟨y, hyR, hAy⟩⟩
      have hSmall : (N R').card < R'.card := by
        have hCard := card_le_card hVs
        rw [card_erase_of_mem hv] at hCard
        have hvr : 0 < (N R).card := card_pos.mpr ⟨v, hv⟩
        change _ < (R.erase x).card
        rw [card_erase_of_mem hx]
        omega
      have hh : P R'.card := ⟨R', (erase_subset _ _).trans hRS, rfl, hSmall⟩
      have hf := Nat.find_min' hP hh
      have hLt : R'.card < R.card := card_erase_lt_of_mem hx
      omega
    obtain ⟨y, hy, hyx, hAy⟩ := hTwo
    have hPair : {x, y} ⊆ G.neighborFinset v := by
      intro w hw
      rcases mem_insert.mp hw with rfl | hw
      · exact (G.mem_neighborFinset v _).mpr hAx
      · obtain rfl := mem_singleton.mp hw
        exact (G.mem_neighborFinset v _).mpr hAy
    have hEq : ({x, y} : Finset V) = G.neighborFinset v := by
      apply eq_of_subset_of_card_le hPair
      rw [card_neighborFinset_eq_degree, card_pair hyx.symm]
      exact (G.degree_le_maxDegree v).trans hmax
    have hz := (G.mem_neighborFinset v z).mpr hAdj
    rw [← hEq] at hz
    rcases mem_insert.mp hz with rfl | hz
    · exact hx
    · obtain rfl := mem_singleton.mp hz
      exact hy
  let T := (S \ R) ∪ N R
  have hIndependent : G.IsIndepSet T := by
    intro v hv w hw hne hAdj
    rcases mem_union.mp hv with hv | hv
    · rcases mem_union.mp hw with hw | hw
      · exact hS.isIndep (mem_sdiff.mp hv).1 (mem_sdiff.mp hw).1 hne hAdj
      · exact (mem_sdiff.mp hv).2 (hFull hw hAdj.symm)
    · rcases mem_union.mp hw with hw | hw
      · exact (mem_sdiff.mp hw).2 (hFull hv hAdj)
      · exact hDisjoint hRS hw (hRS (hFull hv hAdj))
  have hDominating : G.IsDominating T := by
    intro v
    by_cases hv : v ∈ R
    · have hpos : 0 < (G.neighborFinset v).card := by
        rw [card_neighborFinset_eq_degree]
        exact hmin.trans_le (G.minDegree_le_degree v)
      obtain ⟨w, hw⟩ := card_pos.mp hpos
      have hAdj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
      exact Or.inr ⟨w, mem_union_right _ (hN.mpr ⟨v, hv, hAdj.symm⟩), hAdj⟩
    · rcases hS.isDominating v with hs | ⟨w, hw, hAdj⟩
      · exact Or.inl (mem_union_left _ (mem_sdiff.mpr ⟨hs, hv⟩))
      · by_cases hwr : w ∈ R
        · exact Or.inl (mem_union_right _ (hN.mpr ⟨w, hwr, hAdj⟩))
        · exact Or.inr ⟨w, mem_union_left _ (mem_sdiff.mpr ⟨hw, hwr⟩), hAdj⟩
  have hsmall : T.card < S.card := by
    have hcard := card_union_le (S \ R) (N R)
    rw [card_sdiff_of_subset hRS] at hcard
    have hcardR := card_le_card hRS
    change ((S \ R) ∪ N R).card < S.card
    omega
  have hOpt : G.indepDominationNumber ≤ T.card :=
    Nat.sInf_le ⟨T, hIndependent, hDominating, rfl⟩
  exact hsmall.not_ge (hS.card_eq.trans_le hOpt)

end OMA.IndependentDominationTwo

theorem OMA.solution : OMA.R_Arxiv_2107_00295_independentDominationEven_R1.H1 := by
  intro V _ _ G _ hmin hmax
  exact OMA.IndependentDominationTwo.solution G hmin hmax
