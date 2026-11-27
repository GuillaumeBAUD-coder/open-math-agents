import OMAReductions.R_Arxiv_2107_00295_independentDominationOdd_R1

/-!
Prune edges at vertices with no leaf neighbor using Lemma 2.1 of Cho, Kim, Kim
and Oum (arXiv:2202.09594). Once every non-leaf has a leaf neighbor, select a
vertex of degree d maximizing the number t of its leaf neighbors. Deleting
its closed neighborhood isolates at most (d-t)t vertices. They can all join
the selected vertex in an independent dominating set. The bound follows by
induction, since t(D-t) is at most the product of the integers nearest D/2.
-/
namespace OMA.DominationBound

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private def nb (S : Finset V) (v : V) := S.filter (G.Adj v)

-- The vertices left isolated after removing v and its neighbors.
private def lost (S : Finset V) (v : V) :=
  S.filter fun x ↦ x ≠ v ∧ nb G S x ⊆ nb G S v

private def Result (G : SimpleGraph V) (S : Finset V) (D B : ℕ) : Prop :=
  ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧
    (∀ x ∈ S, x ∈ I ∨ ∃ y ∈ I, G.Adj x y) ∧ (B+D)*I.card ≤ B*S.card

private lemma extend {S : Finset V} {D B : ℕ}
    {v : V} (hv : v ∈ S)
    (hgood : D * ((lost G S v).card+1) ≤ B * (nb G S v).card)
    (hr : ∀ R ⊂ S, (∀ x ∈ R, (nb G R x).Nonempty) → Result G R D B) :
    Result G S D B := by
  classical
  let N := nb G S v
  let Z := lost G S v
  let A := insert v N
  let R := (S \ A) \ Z
  change D * (Z.card + 1) ≤ B * N.card at hgood
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
  obtain ⟨I,hd,hi,hdom,hcard⟩ := hr R rsub rnb
  let C := insert v (Z ∪ I)
  have cmem {x : V} : x ∈ C ↔ x = v ∨ x ∈ Z ∨ x ∈ I := by simp [C]
  have dmem {x : V} (hx : x ∈ I) := rmem.mp (hd hx)
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
  · have hc : C.card ≤ (Z ∪ I).card + 1 := card_insert_le _ _
    have hu := card_union_le Z I
    have ha : A.card = N.card + 1 := card_insert_of_notMem vn
    have hz : R.card + Z.card = (S \ A).card := card_sdiff_add_card_eq_card zsub
    have hrest := card_sdiff_add_card_eq_card asub
    have hci : C.card ≤ Z.card + I.card + 1 := by omega
    have hc' := Nat.mul_le_mul_left (B+D) hci
    have hsc : R.card + Z.card + (N.card+1) = S.card := by omega
    rw [← hsc]
    nlinarith

private def leaves (S : Finset V) (v : V) :=
  (nb G S v).filter fun w ↦ (nb G S w).card = 1

-- A non-leaf outside the closed neighborhood cannot lose its own leaf.
private lemma loss_bound {S : Finset V} (hn : ∀ x ∈ S, (nb G S x).Nonempty)
    (hl : ∀ x ∈ S, 2 ≤ (nb G S x).card → (leaves G S x).Nonempty)
    {v : V} (hv : v ∈ S) (hmax : ∀ x ∈ S, (leaves G S x).card ≤ (leaves G S v).card) :
    (lost G S v).card ≤ ((nb G S v).card - (leaves G S v).card) * (leaves G S v).card := by
  classical
  let N := nb G S
  let L := leaves G S
  let Z := lost G S v
  have nm {x y : V} : y ∈ N x ↔ y ∈ S ∧ G.Adj x y := mem_filter
  have lm {x y : V} : y ∈ L x ↔ y ∈ N x ∧ (N y).card = 1 := mem_filter
  have sub : Z ⊆ ((N v) \ L v).biUnion L := by
    intro x hx
    obtain ⟨hxs,hxv,hsub⟩ : x ∈ S ∧ x ≠ v ∧ N x ⊆ N v := mem_filter.mp hx
    have deg2 {y : V} (hy : y ∈ N x) : 2 ≤ (N y).card := by
      have hys := (nm.mp hy).1
      have hyx := nm.mpr ⟨hxs,(nm.mp hy).2.symm⟩
      have hyv := nm.mpr ⟨hv,(nm.mp (hsub hy)).2.symm⟩
      have h : ({x,v} : Finset V) ⊆ N y := by
        intro a ha
        rcases mem_insert.mp ha with rfl | h
        · exact hyx
        · exact mem_singleton.mp h ▸ hyv
      simpa [card_pair hxv] using card_le_card h
    have hxc : (N x).card = 1 := by
      have hp := card_pos.mpr (hn x hxs)
      change 0 < (N x).card at hp
      by_contra! h
      obtain ⟨y,hy⟩ := hl x hxs (by change 2 ≤ (N x).card; omega)
      obtain ⟨hy',hc⟩ := lm.mp hy
      have := deg2 hy'
      omega
    obtain ⟨y,hy⟩ := hn x hxs
    have hnot : y ∉ L v := fun h ↦ (by have := deg2 hy; have := (lm.mp h).2; omega)
    exact mem_biUnion.mpr ⟨y,mem_sdiff.mpr ⟨hsub hy,hnot⟩,lm.mpr ⟨nm.mpr ⟨hxs,(nm.mp hy).2.symm⟩,hxc⟩⟩
  have hle : L v ⊆ N v := filter_subset _ _
  change Z.card ≤ ((N v).card - (L v).card) * (L v).card
  calc Z.card ≤ _ := card_le_card sub
       _ ≤ ∑ x ∈ (N v) \ L v, (L x).card := card_biUnion_le
       _ ≤ ∑ _x ∈ (N v) \ L v, (L v).card := sum_le_sum fun x hx ↦ hmax x (nm.mp (mem_sdiff.mp hx).1).1
       _ = _ := by rw [sum_const, smul_eq_mul, card_sdiff_of_subset hle]

-- For fixed t the inequality is linear in d. Its endpoint at d=D follows
-- by maximizing t(D-t) at the two integers closest to D/2.
private lemma ratio {D d t k : ℕ} (hD : D = 2*k+1) (hk : 2 ≤ k)
    (hd : 1 ≤ d) (hdD : d ≤ D) (htd : t ≤ d) :
    D * ((d-t)*t+1) ≤ (k*(k+1)+1)*d := by
  let B := k*(k+1)+1
  have hb : D ≤ B := by dsimp [B]; nlinarith
  by_cases ht : t = 0
  · subst t; simp; exact hb.trans (by simpa using Nat.mul_le_mul_left B hd)
  have hmax : (D-t)*t ≤ k*(k+1) := by
    have he : D-t+t = D := Nat.sub_add_cancel (htd.trans hdD)
    zify at he hD ⊢
    rcases le_or_gt t k with h | h
    · have h₁ : (0:ℤ) ≤ (k:ℤ)-t := by omega
      nlinarith [mul_nonneg h₁ (show (0:ℤ) ≤ (k:ℤ)+1-t by omega),
        congrArg (fun z : ℤ ↦ z*t) he, congrArg (fun z : ℤ ↦ z*t) hD]
    · have h₁ : (0:ℤ) ≤ (t:ℤ)-(k+1) := by omega
      nlinarith [mul_nonneg h₁ (show (0:ℤ) ≤ (t:ℤ)-k by omega),
        congrArg (fun z : ℤ ↦ z*t) he, congrArg (fun z : ℤ ↦ z*t) hD]
  have he : d-t+t=d := Nat.sub_add_cancel htd
  have he' : D-t+t=D := Nat.sub_add_cancel (htd.trans hdD)
  have hr : D-d+d=D := Nat.sub_add_cancel hdD
  change D*((d-t)*t+1) ≤ B*d
  by_cases h : D*t ≤ B
  · have h₁ := Nat.mul_le_mul_right (d-t) h
    have h₂ := Nat.mul_le_mul_left B (show 1 ≤ t by omega)
    nlinarith
  · have h₁ := Nat.mul_le_mul_right (D-d) (show B ≤ D*t by omega)
    have h₂ : D*((D-t)*t+1) ≤ D*B := Nat.mul_le_mul_left D (by dsimp [B]; omega)
    nlinarith

-- Cho, Kim, Kim and Oum (arXiv:2202.09594, Lemma 2.1) keep just
-- one edge at v. A solution of the smaller graph lifts without growing.
private def cut (v w : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (x = v → y = w) ∧ (y = v → x = w)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h ↦ h.1.ne rfl⟩

private lemma lift_cut {v w : V} {S : Finset V} {D B : ℕ} (hw : w ∈ S) :
    Result (cut G v w) S D B → Result G S D B := by
  classical
  rintro ⟨I,hI,hi,hdom,hcard⟩
  have domG (x : V) (hx : x ∈ S) : x ∈ I ∨ ∃ y ∈ I, G.Adj x y :=
    (hdom x hx).imp_right fun ⟨y,hy,h⟩ ↦ ⟨y,hy,h.1⟩
  by_cases hind : G.IsIndepSet (I : Set V)
  · exact ⟨I,hI,hind,domG,hcard⟩
  let E := I.erase v
  have emem {x : V} : x ∈ E ↔ x ≠ v ∧ x ∈ I := mem_erase
  have ie : G.IsIndepSet (E : Set V) := by
    intro x hx y hy hne h
    exact hi (emem.mp hx).2 (emem.mp hy).2 hne
      ⟨h,fun h ↦ False.elim ((emem.mp hx).1 h),fun h ↦ False.elim ((emem.mp hy).1 h)⟩
  have hvI : v ∈ I := by
    by_contra hv
    apply hind
    simpa [E,erase_eq_of_notMem hv] using ie
  obtain ⟨q,hq,hvq⟩ : ∃ q ∈ E, G.Adj v q := by
    by_contra! h
    apply hind
    intro x hx y hy hne ha
    by_cases hxv : x = v
    · subst x
      exact h y (emem.mpr ⟨hne.symm,hy⟩) ha
    by_cases hyv : y = v
    · subst y
      exact h x (emem.mpr ⟨hne,hx⟩) ha.symm
    exact ie (emem.mpr ⟨hxv,hx⟩) (emem.mpr ⟨hyv,hy⟩) hne ha
  have esub : E ⊆ S := (erase_subset v I).trans hI
  have ec : E.card+1 = I.card := card_erase_add_one hvI
  have edom (x : V) (hx : x ∈ S) (hxw : x ≠ w) : x ∈ E ∨ ∃ y ∈ E, G.Adj x y := by
    by_cases hxv : x = v
    · subst x; exact Or.inr ⟨q,hq,hvq⟩
    rcases hdom x hx with h | ⟨y,hy,ha⟩
    · exact Or.inl (emem.mpr ⟨hxv,h⟩)
    · exact Or.inr ⟨y,emem.mpr ⟨fun h ↦ hxw (ha.2.2 h),hy⟩,ha.1⟩
  by_cases h : w ∈ E ∨ ∃ y ∈ E, G.Adj w y
  · refine ⟨E,esub,ie,?_,(Nat.mul_le_mul_left _ (by omega : E.card ≤ I.card)).trans hcard⟩
    intro x hx
    by_cases he : x = w
    · simpa [he] using h
    · exact edom x hx he
  · refine ⟨insert w E,insert_subset hw esub,?_,?_,?_⟩
    · intro x hx y hy hne hxy
      rcases mem_insert.mp hx with rfl | hxE <;> rcases mem_insert.mp hy with rfl | hyE
      · exact hne rfl
      · exact h (Or.inr ⟨y,hyE,hxy⟩)
      · exact h (Or.inr ⟨x,hxE,hxy.symm⟩)
      · exact ie hxE hyE hne hxy
    · intro x hx
      by_cases he : x = w
      · exact Or.inl (mem_insert.mpr (Or.inl he))
      rcases edom x hx he with h | ⟨y,hy,hxy⟩
      · exact Or.inl (mem_insert_of_mem h)
      · exact Or.inr ⟨y,mem_insert_of_mem hy,hxy⟩
    · exact (Nat.mul_le_mul_left _ ((card_insert_le w E).trans_eq ec)).trans hcard

private noncomputable def measure [Fintype V] (G : SimpleGraph V) (S : Finset V) : ℕ := by
  exact S.card + G.edgeSet.ncard

private lemma solve (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype V] (D k : ℕ) (hD : D = 2*k+1) (hk : 2 ≤ k)
    (S : Finset V) (hn : ∀ x ∈ S, (nb G S x).Nonempty)
    (hd : ∀ x ∈ S, (nb G S x).card ≤ D) : Result G S D (k*(k+1)+1) := by
  classical
  let B := k*(k+1)+1
  by_cases hS : S.Nonempty
  case neg =>
    rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    exact ⟨∅, by simp, by simp [SimpleGraph.IsIndepSet], by simp, by simp⟩
  by_cases hl : ∀ x ∈ S, 2 ≤ (nb G S x).card → (leaves G S x).Nonempty
  · obtain ⟨v,hv,hm⟩ := S.exists_max_image (fun x ↦ (leaves G S x).card) hS
    have h₁ := loss_bound G hn hl hv hm
    have h₂ := ratio hD hk (card_pos.mpr (hn v hv)) (hd v hv)
      (card_le_card (show leaves G S v ⊆ nb G S v from filter_subset _ _))
    apply extend G hv ((Nat.mul_le_mul_left D (Nat.add_le_add_right h₁ 1)).trans h₂)
    intro R hR hr
    have hlt : measure G R < measure G S := by
      dsimp [measure]; exact Nat.add_lt_add_right (card_lt_card hR) _
    apply solve G D k hD hk R hr
    intro x hx
    exact (card_le_card (filter_subset_filter _ (Finset.ssubset_iff_subset_ne.mp hR).1)).trans
      (hd x ((Finset.ssubset_iff_subset_ne.mp hR).1 hx))
  · push Not at hl
    obtain ⟨v,hv,hvc,hvl⟩ := hl
    obtain ⟨w,hw⟩ := hn v hv
    let K := cut G v w
    have nm {x y : V} : y ∈ nb G S x ↔ y ∈ S ∧ G.Adj x y := mem_filter
    have km {x y : V} : y ∈ nb K S x ↔ y ∈ S ∧ G.Adj x y ∧
        (x = v → y = w) ∧ (y = v → x = w) := mem_filter
    have hws := (nm.mp hw).1
    have hvw := (nm.mp hw).2
    have hnonleaf {y : V} (hy : y ∈ nb G S v) : 2 ≤ (nb G S y).card := by
      have hpos := card_pos.mpr (hn y (nm.mp hy).1)
      by_contra! hh
      have hyL : y ∈ leaves G S v := mem_filter.mpr ⟨hy,by omega⟩
      simp_all
    have hK : ∀ x ∈ S, (nb K S x).Nonempty := by
      intro x hx
      by_cases hxv : x = v
      · subst x
        exact ⟨w, km.mpr ⟨hws,hvw,fun _ ↦ rfl,fun h ↦ h.symm⟩⟩
      by_cases hxa : G.Adj v x
      · have hc := hnonleaf (nm.mpr ⟨hx,hxa⟩)
        have hh := card_erase_of_mem (nm.mpr ⟨hv,hxa.symm⟩)
        obtain ⟨y,hy⟩ := card_pos.mp (show 0 < ((nb G S x).erase v).card by omega)
        obtain ⟨hyv,hy'⟩ := mem_erase.mp hy
        exact ⟨y,km.mpr ⟨(nm.mp hy').1,(nm.mp hy').2,fun h ↦ False.elim (hxv h),
          fun h ↦ False.elim (hyv h)⟩⟩
      · obtain ⟨y,hy⟩ := hn x hx
        obtain ⟨hys,hxy⟩ := nm.mp hy
        exact ⟨y,km.mpr ⟨hys,hxy,fun h ↦ False.elim (hxv h),
          fun h ↦ False.elim (hxa (h ▸ hxy.symm))⟩⟩
    have hle : K ≤ G := fun _ _ h ↦ h.1
    have hstrict : K < G := by
      refine lt_iff_le_not_ge.mpr ⟨hle,?_⟩
      intro hback
      have he := card_erase_of_mem hw
      obtain ⟨z,hz⟩ := card_pos.mp (show 0 < ((nb G S v).erase w).card by omega)
      obtain ⟨hzw,hz'⟩ := mem_erase.mp hz
      exact hzw ((hback (nm.mp hz').2).2.1 rfl)
    have hlt : measure K S < measure G S := by
      dsimp [measure]
      apply Nat.add_lt_add_left
      exact Set.ncard_lt_ncard (edgeSet_strict_mono hstrict)
    apply lift_cut G (v := v) hws
    apply solve K D k hD hk S hK
    intro x hx
    exact (card_le_card (show nb K S x ⊆ nb G S x from
      fun y hy ↦ nm.mpr ⟨(km.mp hy).1,(km.mp hy).2.1⟩)).trans (hd x hx)
termination_by measure G S
decreasing_by all_goals assumption

end OMA.DominationBound

open Finset SimpleGraph

theorem OMA.solution : OMA.R_Arxiv_2107_00295_independentDominationOdd_R1.H2 := by
  intro V _ _ G _ D hD hodd hmin hmax _
  obtain ⟨k,he⟩ := hodd
  have hk : 2 ≤ k := by omega
  let B := k*(k+1)+1
  have hnb (x : V) : OMA.DominationBound.nb G univ x = G.neighborFinset x := by
    ext y
    simp [OMA.DominationBound.nb]
  have hn : ∀ x ∈ (univ : Finset V), (OMA.DominationBound.nb G univ x).Nonempty := by
    intro x _
    rw [hnb, ← card_pos, card_neighborFinset_eq_degree]
    exact hmin.trans_le (G.minDegree_le_degree _)
  have hd : ∀ x ∈ (univ : Finset V), (OMA.DominationBound.nb G univ x).card ≤ D := by
    intro x _
    rw [hnb, card_neighborFinset_eq_degree]
    exact (G.degree_le_maxDegree x).trans hmax
  obtain ⟨I,_,hi,hdom,hc⟩ := OMA.DominationBound.solve G D k (by omega) hk univ hn hd
  have hI : G.IsNIndepDominatingSet I.card I := ⟨hi,fun x ↦ hdom x (mem_univ x),rfl⟩
  have hle : G.indepDominationNumber ≤ I.card := Nat.sInf_le ⟨I,hI⟩
  have hm : (D+2)^2 = 4*(B+D)+1 := by dsimp [B]; rw [he]; ring
  have hh : (D+2)^2/4 = B+D := by omega
  dsimp only
  rw [hh, Nat.add_sub_cancel]
  simpa [B] using (Nat.mul_le_mul_left (B+D) hle).trans hc
