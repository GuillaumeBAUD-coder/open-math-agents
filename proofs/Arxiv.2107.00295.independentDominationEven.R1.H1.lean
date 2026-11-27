import OMAReductions.R_Arxiv_2107_00295_independentDominationEven_R1

/-! In maximum degree two a minimum dominating set can be made independent.
Replace a vertex with an internal neighbor by its unique private neighbor. -/

open Finset SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private lemma only_two {x y p z : V} (hdeg : G.degree x ≤ 2)
    (hy : G.Adj x y) (hp : G.Adj x p) (hz : G.Adj x z) (hpy : p ≠ y) (hzy : z ≠ y) :
    z = p := by
  by_contra hn
  have hs : ({z,p,y} : Finset V) ⊆ G.neighborFinset x := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> simpa
  have hc := card_le_card hs
  rw [card_neighborFinset_eq_degree] at hc
  simp [hn, hpy, hzy] at hc
  omega

theorem OMA.solution : OMA.R_Arxiv_2107_00295_independentDominationEven_R1.H1 := by
  intro V _ _ G _ hmin hmax
  classical
  let bad (S : Finset V) := S.filter (fun v => ∃ w ∈ S, G.Adj v w)
  let sets := (univ : Finset (Finset V)).filter (fun S => G.IsNDominatingSet G.dominationNumber S)
  obtain ⟨A,hA⟩ := G.exists_isNDominatingSet_dominationNumber
  have hn : sets.Nonempty := ⟨A, by simpa [sets] using hA⟩
  obtain ⟨S, hS, opt⟩ := exists_min_image sets (fun S => (bad S).card) hn
  have hdom : G.IsNDominatingSet G.dominationNumber S := by simpa [sets] using hS
  have hind : G.IsIndepSet (↑S : Set V) := by
    intro x hx y hy hxy hAdj
    change x ∈ S at hx
    change y ∈ S at hy
    let T := S.erase x
    have hyT : y ∈ T := mem_erase.mpr ⟨hxy.symm, hy⟩
    let covered (z : V) := z ∈ T ∨ ∃ w ∈ T, G.Adj z w
    have hnot : ¬ ∀ z, covered z := by
      intro hc
      have hle := G.dominationNumber_le_of_isDominating T hc
      have hlt := card_erase_lt_of_mem hx
      rw [hdom.card_eq] at hlt
      exact (not_le_of_gt hlt) hle
    obtain ⟨p,hp⟩ := not_forall.mp hnot
    have priv (z : V) (hz : ¬ covered z) : z ∉ S ∧ G.Adj x z := by
      have hzx : z ≠ x := by rintro rfl; exact hz (Or.inr ⟨y,hyT,hAdj⟩)
      have hzS : z ∉ S := fun h => hz (Or.inl (mem_erase.mpr ⟨hzx,h⟩))
      refine ⟨hzS, ?_⟩
      obtain ⟨w,hw,hwz⟩ := (hdom.isDominating z).resolve_left hzS
      by_cases hwx : w = x
      · simpa [hwx] using hwz.symm
      · exact (hz (Or.inr ⟨w, mem_erase.mpr ⟨hwx,hw⟩, hwz⟩)).elim
    have hp' := priv p hp
    have hunique (z : V) (hz : ¬ covered z) : z = p :=
      only_two G ((G.degree_le_maxDegree x).trans hmax) hAdj hp'.2 (priv z hz).2
        (fun h => hp'.1 (h ▸ hy)) (fun h => (priv z hz).1 (h ▸ hy))
    let R := insert p T
    have hR : G.IsNDominatingSet G.dominationNumber R := by
      constructor
      · intro z
        by_cases hz : covered z
        · rcases hz with hz | ⟨w,hw,hadj⟩
          · exact Or.inl (mem_insert_of_mem hz)
          · exact Or.inr ⟨w, mem_insert_of_mem hw, hadj⟩
        · exact Or.inl (by rw [hunique z hz]; exact mem_insert_self _ _)
      · have hpT : p ∉ T := fun h => hp (Or.inl h)
        simpa [R, T, hpT, card_erase_of_mem hx, Nat.sub_add_cancel (card_pos.mpr ⟨x,hx⟩)] using hdom.card_eq
    have hsub : bad R ⊆ (bad S).erase x := by
      intro z hz
      obtain ⟨hzR,w,hwR,hadj⟩ := mem_filter.mp hz
      have hzT : z ∈ T := by
        rcases mem_insert.mp hzR with rfl | ht
        · rcases mem_insert.mp hwR with rfl | hw
          · exact (hadj.ne rfl).elim
          · exact (hp (Or.inr ⟨w,hw,hadj⟩)).elim
        · exact ht
      have hwT : w ∈ T := by
        rcases mem_insert.mp hwR with rfl | ht
        · exact (hp (Or.inr ⟨z,hzT,hadj.symm⟩)).elim
        · exact ht
      exact mem_erase.mpr ⟨(mem_erase.mp hzT).1,
        mem_filter.mpr ⟨(mem_erase.mp hzT).2,w,(mem_erase.mp hwT).2,hadj⟩⟩
    have hxB : x ∈ bad S := mem_filter.mpr ⟨hx,y,hy,hAdj⟩
    have hlt := (card_le_card hsub).trans_lt (card_erase_lt_of_mem hxB)
    exact (not_le_of_gt hlt) (opt R (by simpa [sets] using hR))
  have hcomp : G.IsDominating (↑(Sᶜ) : Set V) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨w,hw⟩ := (G.degree_pos_iff_exists_adj v).mp (hmin.trans_le (G.minDegree_le_degree v))
      exact Or.inr ⟨w, mem_compl.mpr (fun hwS => hind hv hwS hw.ne hw), hw⟩
    · exact Or.inl (mem_compl.mpr hv)
  have hInd : G.indepDominationNumber ≤ S.card :=
    Nat.sInf_le (show ∃ D, G.IsNIndepDominatingSet S.card D from ⟨S,hind,hdom.isDominating,rfl⟩)
  have hc := G.dominationNumber_le_of_isDominating Sᶜ hcomp
  rw [← hdom.card_eq, card_compl] at hc
  have := S.card_le_univ
  omega
