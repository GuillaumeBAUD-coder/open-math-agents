import OMAReductions.R_Arxiv_2107_00295_independentDominationOdd_R1

/-! In a subcubic graph without isolated vertices, one may choose a vertex
such that deleting its closed neighborhood isolates fewer vertices than its
degree. Add that vertex and the new isolated vertices to the independent
dominating set, then recurse on the remainder. -/

namespace OMA.Subcubic

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private def nb (S : Finset V) (v : V) := S.filter (G.Adj v)

-- The vertices left isolated after removing v and its neighbors.
private def lost (S : Finset V) (v : V) :=
  S.filter fun x ↦ x ≠ v ∧ nb G S x ⊆ nb G S v

private lemma good {S : Finset V} (hS : S.Nonempty)
    (hn : ∀ v ∈ S, (nb G S v).Nonempty) (hdeg : ∀ v ∈ S, (nb G S v).card ≤ 3) :
    ∃ v ∈ S, (lost G S v).card < (nb G S v).card := by
  classical
  let N := nb G S
  let Z := lost G S
  have nmem (x y : V) : y ∈ N x ↔ y ∈ S ∧ G.Adj x y := mem_filter
  have zmem (x y : V) : y ∈ Z x ↔ y ∈ S ∧ y ≠ x ∧ N y ⊆ N x := mem_filter
  obtain ⟨v, hv, hmin⟩ := S.exists_min_image (fun x ↦ (N x).card) hS
  by_cases hgood : (Z v).card < (N v).card
  · exact ⟨v,hv,hgood⟩
  let T := insert v (Z v)
  have hTcard : T.card = (Z v).card + 1 := card_insert_of_notMem (by simp [Z,lost])
  have htwin {t : V} (ht : t ∈ T) : t ∈ S ∧ N t = N v := by
    rcases mem_insert.mp ht with rfl | ht
    · exact ⟨hv,rfl⟩
    obtain ⟨hts, _, hs⟩ := (zmem _ _).mp ht
    exact ⟨hts,eq_of_subset_of_card_le hs (hmin t hts)⟩
  obtain ⟨w,hw⟩ := hn v hv
  change w ∈ N v at hw
  have hws := ((nmem _ _).mp hw).1
  have hsub : T ⊆ N w := by
    intro t ht
    obtain ⟨hts,heq⟩ := htwin ht
    exact (nmem _ _).mpr ⟨hts, (((nmem _ _).mp (heq.symm ▸ hw)).2).symm⟩
  have hcount := card_le_card hsub
  have hwdeg := hdeg w hws
  have hpos := card_pos.mpr (hn v hv)
  change 0 < (N v).card at hpos
  change (N w).card ≤ 3 at hwdeg
  -- Any vertex touching a twin of v belongs to the common neighborhood of v.
  have touch {x t : V} (hx : x ∈ S) (ht : t ∈ T) (hxt : G.Adj x t) : x ∈ N v := by
    rw [← (htwin ht).2]
    exact (nmem _ _).mpr ⟨hx,hxt.symm⟩
  refine ⟨w,hws,?_⟩
  change (Z w).card < (N w).card
  by_cases hall : T = N w
  · have hsubset : Z w ⊆ (N v).erase w := by
      intro x hx
      obtain ⟨hxs,hxw,hxn⟩ := (zmem _ _).mp hx
      obtain ⟨t,ht⟩ := hn x hxs
      exact mem_erase.mpr ⟨hxw, touch hxs (hall.symm ▸ hxn ht) ((nmem _ _).mp ht).2⟩
    have h := card_le_card hsubset
    rw [card_erase_of_mem hw] at h
    omega
  · have hlt : T.card < (N w).card :=
      lt_of_not_ge (fun h ↦ hall (eq_of_subset_of_card_le hsub h))
    have hc : ((N w) \ T).card = 1 := by rw [card_sdiff_of_subset hsub]; omega
    obtain ⟨y,hy⟩ := card_eq_one.mp hc
    have hyw : y ∈ N w := (mem_sdiff.mp (show y ∈ N w \ T by simp [hy])).1
    have hys := ((nmem _ _).mp hyw).1
    have hwy := (nmem y w).mpr ⟨hws,((nmem _ _).mp hyw).2.symm⟩
    have hvnum : (N v).card ≤ 1 := by omega
    have hvone : N v = {w} := eq_of_subset_of_card_le (singleton_subset_iff.mpr hw)
      (by simpa only [card_singleton] using hvnum) |>.symm
    have hsubset : Z w ⊆ (N y).erase w := by
      intro x hx
      obtain ⟨hxs,hxw,hxn⟩ := (zmem _ _).mp hx
      obtain ⟨t,ht⟩ := hn x hxs
      have ha := ((nmem _ _).mp ht).2
      have hnot : t ∉ T := by
        intro h
        have h' := touch hxs h ha
        exact hxw (by simpa [hvone] using h')
      have hty : t = y := by
        have h := mem_sdiff.mpr ⟨hxn ht,hnot⟩
        simpa [hy] using h
      subst t
      exact mem_erase.mpr ⟨hxw, (nmem _ _).mpr ⟨hxs,ha.symm⟩⟩
    have h := card_le_card hsubset
    have hydeg := hdeg y hys
    change (N y).card ≤ 3 at hydeg
    rw [card_erase_of_mem hwy] at h
    omega

private lemma solve (S : Finset V) (hn : ∀ v ∈ S, (nb G S v).Nonempty)
    (hdeg : ∀ v ∈ S, (nb G S v).card ≤ 3) :
    ∃ D ⊆ S, G.IsIndepSet (D : Set V) ∧
      (∀ x ∈ S, x ∈ D ∨ ∃ y ∈ D, G.Adj x y) ∧ 2 * D.card ≤ S.card := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S.Nonempty
    case neg =>
      rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      exact ⟨∅, by simp, by simp [SimpleGraph.IsIndepSet], by simp, by simp⟩
    obtain ⟨v,hv,hgood⟩ := good G hS hn hdeg
    let N := nb G S v
    let Z := lost G S v
    let A := insert v N
    let R := (S \ A) \ Z
    change Z.card < N.card at hgood
    have nmem {x : V} : x ∈ N ↔ x ∈ S ∧ G.Adj v x := mem_filter
    have zmem {x : V} : x ∈ Z ↔ x ∈ S ∧ x ≠ v ∧ nb G S x ⊆ N := mem_filter
    have vn : v ∉ N := fun h ↦ G.loopless.irrefl v (nmem.mp h).2
    have vz : v ∉ Z := fun h ↦ (zmem.mp h).2.1 rfl
    have nadj {x y : V} (hx : x ∈ Z) (hy : y ∈ S) (ha : G.Adj x y) : y ∈ N :=
      (zmem.mp hx).2.2 (mem_filter.mpr ⟨hy,ha⟩)
    have zn {x : V} (hx : x ∈ Z) : x ∉ N := fun h ↦
      vn (nadj hx hv (nmem.mp h).2.symm)
    have amem {x : V} : x ∈ A ↔ x = v ∨ x ∈ N := mem_insert
    have asub : A ⊆ S := fun x hx ↦ (amem.mp hx).elim (fun h ↦ h ▸ hv) (fun h ↦ (nmem.mp h).1)
    have zsub : Z ⊆ S \ A := fun x hx ↦ mem_sdiff.mpr
      ⟨(zmem.mp hx).1, fun h ↦ (amem.mp h).elim (zmem.mp hx).2.1 (zn hx)⟩
    have rmem {x : V} : x ∈ R ↔ x ∈ S ∧ x ≠ v ∧ x ∉ N ∧ x ∉ Z := by
      simp [R,A,and_assoc,not_or]
    have rsub : R ⊂ S := Finset.ssubset_iff_subset_ne.mpr
      ⟨fun x hx ↦ (rmem.mp hx).1, fun h ↦ (rmem.mp (h.symm ▸ hv)).2.1 rfl⟩
    have rnb : ∀ x ∈ R, (nb G R x).Nonempty := by
      intro x hx
      obtain ⟨hxs,hxv,hxn,hxz⟩ := rmem.mp hx
      have hnot : ¬ nb G S x ⊆ N := fun h ↦ hxz (zmem.mpr ⟨hxs,hxv,h⟩)
      obtain ⟨y,hy,hyN⟩ := Finset.not_subset.mp hnot
      obtain ⟨hys,hxy⟩ := mem_filter.mp hy
      have hyv : y ≠ v := by
        rintro rfl
        exact hxn (nmem.mpr ⟨hxs,hxy.symm⟩)
      have hyz : y ∉ Z := fun h ↦ hxn (nadj h hxs hxy.symm)
      exact ⟨y,mem_filter.mpr ⟨rmem.mpr ⟨hys,hyv,hyN,hyz⟩,hxy⟩⟩
    have rdeg : ∀ x ∈ R, (nb G R x).card ≤ 3 := by
      intro x hx
      exact (card_le_card (filter_subset_filter _ (Finset.ssubset_iff_subset_ne.mp rsub).1)).trans
        (hdeg x (rmem.mp hx).1)
    obtain ⟨D,hd,hi,hdom,hcard⟩ := ih R rsub rnb rdeg
    let C := insert v (Z ∪ D)
    have cmem {x : V} : x ∈ C ↔ x = v ∨ x ∈ Z ∨ x ∈ D := by simp [C]
    have dmem {x : V} (hx : x ∈ D) := rmem.mp (hd hx)
    refine ⟨C, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases cmem.mp hx with rfl | h | h
      · exact hv
      · exact (zmem.mp h).1
      · exact (dmem h).1
    · intro x hx y hy hne hxy
      change x ∈ C at hx
      change y ∈ C at hy
      rcases cmem.mp hx with rfl | hxZ | hxD <;> rcases cmem.mp hy with rfl | hyZ | hyD
      · exact hne rfl
      · exact zn hyZ (nmem.mpr ⟨(zmem.mp hyZ).1,hxy⟩)
      · exact (dmem hyD).2.2.1 (nmem.mpr ⟨(dmem hyD).1,hxy⟩)
      · exact zn hxZ (nmem.mpr ⟨(zmem.mp hxZ).1,hxy.symm⟩)
      · exact zn hyZ (nadj hxZ (zmem.mp hyZ).1 hxy)
      · exact (dmem hyD).2.2.1 (nadj hxZ (dmem hyD).1 hxy)
      · exact (dmem hxD).2.2.1 (nmem.mpr ⟨(dmem hxD).1,hxy.symm⟩)
      · exact (dmem hxD).2.2.1 (nadj hyZ (dmem hxD).1 hxy.symm)
      · exact hi hxD hyD hne hxy
    · intro x hxs
      by_cases hx : x ∈ C
      · exact Or.inl hx
      right
      by_cases hn : x ∈ N
      · exact ⟨v,cmem.mpr (Or.inl rfl),(nmem.mp hn).2.symm⟩
      have hxv : x ≠ v := fun h ↦ hx (cmem.mpr (Or.inl h))
      have hxz : x ∉ Z := fun h ↦ hx (cmem.mpr (Or.inr (Or.inl h)))
      rcases hdom x (rmem.mpr ⟨hxs,hxv,hn,hxz⟩) with h | ⟨y,hy,hxy⟩
      · exact False.elim (hx (cmem.mpr (Or.inr (Or.inr h))))
      · exact ⟨y,cmem.mpr (Or.inr (Or.inr hy)),hxy⟩
    · have hc : C.card ≤ (Z ∪ D).card + 1 := card_insert_le _ _
      have hu := card_union_le Z D
      have ha : A.card = N.card + 1 := card_insert_of_notMem vn
      have hz : R.card + Z.card = (S \ A).card := card_sdiff_add_card_eq_card zsub
      have hrest := card_sdiff_add_card_eq_card asub
      omega

end OMA.Subcubic


open Finset SimpleGraph

theorem OMA.solution : OMA.R_Arxiv_2107_00295_independentDominationOdd_R1.H1 := by
  intro V _ _ G _ hmin hmax
  classical
  have hnb (x : V) : OMA.Subcubic.nb G univ x = G.neighborFinset x := by
    ext y
    simp [OMA.Subcubic.nb]
  have hn : ∀ x ∈ (univ : Finset V), (OMA.Subcubic.nb G univ x).Nonempty := by
    intro x _
    rw [hnb, ← card_pos, card_neighborFinset_eq_degree]
    exact hmin.trans_le (G.minDegree_le_degree _)
  have hd : ∀ x ∈ (univ : Finset V), (OMA.Subcubic.nb G univ x).card ≤ 3 := by
    intro x _
    rw [hnb, card_neighborFinset_eq_degree]
    exact (G.degree_le_maxDegree x).trans hmax
  obtain ⟨D, _, hi, hdom, hc⟩ := OMA.Subcubic.solve G univ hn hd
  have hD : G.IsNIndepDominatingSet D.card D := ⟨hi, fun x ↦ hdom x (mem_univ x), rfl⟩
  have hle : G.indepDominationNumber ≤ D.card := Nat.sInf_le ⟨D,hD⟩
  simpa using (Nat.mul_le_mul_left 2 hle).trans hc
