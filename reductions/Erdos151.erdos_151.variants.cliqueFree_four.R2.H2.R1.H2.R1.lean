import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R1

/-! Elimination of edges of triangle multiplicity at most two in a partial edge coloring.
A stalled extension has a tree of triangles with opposite signs across its shared
light edges. Its heavy edges span every vertex cut that crosses the tree.

The final passage from a coloring to a transversal adapts the merged R2 reduction
by @dk8827. -/

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R1_H2_R1

private def Mixed {α : Type*} (c : α → Bool) (s : Finset α) : Prop :=
  ∃ x ∈ s, ∃ y ∈ s, c x ≠ c y

/-- Color a representative opposite an edge outside the remaining representatives.
Three incidences per triangle and at most two per representative guarantee such an edge. -/
private theorem fill_representatives {ι α : Type*} [DecidableEq α] [DecidableEq ι]
    (E : ι → Finset α) (f : ι → α) (T : Finset ι)
    (hf : Function.Injective f) (hmem : ∀ t ∈ T, f t ∈ E t)
    (hsize : ∀ t ∈ T, (E t).card = 3)
    (hdeg : ∀ t ∈ T, (T.filter fun u => f t ∈ E u).card ≤ 2)
    (p : α → Bool) :
    ∃ c : α → Bool, (∀ x ∉ T.image f, c x = p x) ∧ ∀ t ∈ T, Mixed c (E t) := by
  classical
  induction T using Finset.strongInduction generalizing p with
  | H T ih =>
    by_cases hT : T.Nonempty
    · obtain ⟨t,ht,x,hx,hout⟩ : ∃ t ∈ T, ∃ x ∈ E t, x ∉ T.image f := by
        by_contra! h
        have hl (u) (hu : u ∈ T) :
            3 ≤ ((T.image f).bipartiteAbove (fun i a => a ∈ E i) u).card := by
          rw [← hsize u hu]
          exact card_le_card fun a ha => mem_filter.mpr ⟨h u hu a ha, ha⟩
        have hr (a) (ha : a ∈ T.image f) :
            (T.bipartiteBelow (fun i b => b ∈ E i) a).card ≤ 2 := by
          obtain ⟨u,hu,rfl⟩ := mem_image.mp ha
          exact hdeg u hu
        have count := card_nsmul_le_card_nsmul (fun i a => a ∈ E i) hl hr
        simp only [smul_eq_mul, card_image_of_injective _ hf] at count
        have := card_pos.mpr hT
        omega
      let q := Function.update p (f t) (!p x)
      obtain ⟨c,hc,hm⟩ := ih (T.erase t) (erase_ssubset ht)
        (fun u hu => hmem u (mem_of_mem_erase hu))
        (fun u hu => hsize u (mem_of_mem_erase hu))
        (fun u hu => (card_le_card (filter_subset_filter _ (erase_subset t T))).trans
          (hdeg u (mem_of_mem_erase hu))) q
      have hft : f t ∉ (T.erase t).image f := by
        rintro h
        obtain ⟨a,ha,he⟩ := mem_image.mp h
        exact (mem_erase.mp ha).1 (hf he)
      have hsub := image_subset_image (f := f) (erase_subset t T)
      refine ⟨c, fun a ha => (hc a (fun h => ha (hsub h))).trans
        (Function.update_of_ne (show a ≠ f t from fun e => ha (e ▸ mem_image_of_mem f ht)) _ _), ?_⟩
      intro u hu
      by_cases he : u = t
      · subst u
        refine ⟨f t,hmem t ht,x,hx,?_⟩
        rw [hc _ hft, hc _ (fun h => hout (hsub h))]
        have hxf : x ≠ f t := fun e => hout (e ▸ mem_image_of_mem f ht)
        simp [q,hxf]
      · exact hm u (mem_erase.mpr ⟨he,hu⟩)
    · exact ⟨p, fun _ _ => rfl, fun t ht => (hT ⟨t,ht⟩).elim⟩

private theorem fill_unforced {ι α : Type*} [DecidableEq α] [DecidableEq ι]
    (E : ι → Finset α) (T : Finset ι) (L : Finset α) (p : α → Bool)
    (hsize : ∀ t ∈ T, (E t).card = 3)
    (hdeg : ∀ x ∈ L, (T.filter fun t => x ∈ E t).card ≤ 2)
    (hfree : ∀ t ∈ T, ¬ Mixed p (E t \ L) → 2 ≤ (E t ∩ L).card) :
    ∃ c : α → Bool, (∀ x ∉ L, c x = p x) ∧ ∀ t ∈ T, Mixed c (E t) := by
  classical
  let U := T.filter fun t => ¬ Mixed p (E t \ L)
  let opt (u : U) := E u.val ∩ L
  have hall (B : Finset U) : B.card ≤ (B.biUnion opt).card := by
    let W := B.biUnion opt
    have left (u) (hu : u ∈ B) : 2 ≤ (W.bipartiteAbove (fun i a => a ∈ opt i) u).card := by
      apply (hfree u.val (mem_filter.mp u.property).1 (mem_filter.mp u.property).2).trans
      exact card_le_card fun a ha => mem_filter.mpr ⟨mem_biUnion.mpr ⟨u,hu,ha⟩,ha⟩
    have right (a) (ha : a ∈ W) : (B.bipartiteBelow (fun i b => b ∈ opt i) a).card ≤ 2 := by
      obtain ⟨u,_,hu⟩ := mem_biUnion.mp ha
      refine (card_le_card_of_injOn Subtype.val ?_ (Subtype.val_injective.injOn)).trans
        (hdeg a (mem_inter.mp hu).2)
      intro i hi
      exact mem_filter.mpr ⟨(mem_filter.mp i.property).1, (mem_inter.mp (mem_filter.mp hi).2).1⟩
    have hc := card_nsmul_le_card_nsmul (fun i a => a ∈ opt i) left right
    change B.card * 2 ≤ W.card * 2 at hc
    change B.card ≤ W.card
    omega
  obtain ⟨f,hf,ho⟩ := (all_card_le_biUnion_card_iff_exists_injective opt).mp hall
  obtain ⟨c,hc,hm⟩ := fill_representatives (fun i : U => E i.val) f univ hf
    (fun i _ => (mem_inter.mp (ho i)).1) (fun i _ => hsize i.val (mem_filter.mp i.property).1)
    (fun i _ => by
      refine (card_le_card_of_injOn Subtype.val ?_ Subtype.val_injective.injOn).trans
        (hdeg _ (mem_inter.mp (ho i)).2)
      intro u hu
      exact mem_filter.mpr ⟨(mem_filter.mp u.property).1, (mem_filter.mp hu).2⟩) p
  have fixed (a) (ha : a ∉ L) : c a = p a := by
    apply hc
    rintro h
    obtain ⟨i,_,rfl⟩ := mem_image.mp h
    exact ha (mem_inter.mp (ho i)).2
  refine ⟨c, fixed, ?_⟩
  intro t ht
  by_cases hu : t ∈ U
  · exact hm ⟨t,hu⟩ (mem_univ _)
  · have h : Mixed p (E t \ L) := by by_contra h; exact hu (mem_filter.mpr ⟨ht,h⟩)
    obtain ⟨a,ha,b,hb,hn⟩ := h
    exact ⟨a,(mem_sdiff.mp ha).1,b,(mem_sdiff.mp hb).1,by
      rwa [fixed _ (mem_sdiff.mp ha).2, fixed _ (mem_sdiff.mp hb).2]⟩


private theorem attach_leaf {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (E : ι → Finset α) (L : Finset α) (W : Finset ι) (r : ι) (x : α)
    (hx : x ∈ E r) (hxW : x ∈ W.biUnion E) (hxL : x ∈ L)
    (hc : (W.biUnion E ∩ L.erase x).card + 1 = W.card)
    (hmin : ∀ B ⊂ W, B.card ≤ (B.biUnion E ∩ L.erase x).card) :
    ∀ B ⊂ insert r W, B.card ≤ (B.biUnion E ∩ L).card := by
  classical
  intro B hB
  have gain (A : Finset ι) (hAB : A ⊆ B) (hxB : x ∈ B.biUnion E) :
      (A.biUnion E ∩ L.erase x).card + 1 ≤ (B.biUnion E ∩ L).card := by
    rw [← card_insert_of_notMem (a := x) (by simp)]
    apply card_le_card
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact mem_inter.mpr ⟨hxB,hxL⟩
    · exact mem_inter.mpr ⟨(by obtain ⟨t,ht,hat⟩ := mem_biUnion.mp (mem_inter.mp ha).1; exact mem_biUnion.mpr ⟨t,hAB ht,hat⟩),
        mem_of_mem_erase (mem_inter.mp ha).2⟩
  by_cases hrB : r ∈ B
  · have hAW : B.erase r ⊂ W := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
      · intro t ht
        exact (mem_insert.mp (hB.le (mem_of_mem_erase ht))).resolve_left (mem_erase.mp ht).1
      · intro he
        exact hB.ne (by rw [← he,insert_erase hrB])
    have h := gain (B.erase r) (erase_subset _ _) (mem_biUnion.mpr ⟨r,hrB,hx⟩)
    have := hmin _ hAW
    have := card_erase_add_one hrB
    omega
  · have hBW : B ⊆ W := fun t ht => (mem_insert.mp (hB.le ht)).resolve_left
        (fun he => hrB (he ▸ ht))
    by_cases he : B = W
    · subst B
      exact hc ▸ gain W Subset.rfl hxW
    · refine (hmin B (Finset.ssubset_iff_subset_ne.mpr ⟨hBW,he⟩)).trans (card_le_card ?_)
      exact inter_subset_inter_left (erase_subset x L)

private def Certificate {ι α : Type*} [DecidableEq α] (E : ι → Finset α)
    (L : Finset α) (p : α → Bool) (W : Finset ι) (b : ι → Bool) : Prop :=
  (W.biUnion E ∩ L).card + 1 = W.card ∧
  (∀ B ⊂ W, B.card ≤ (B.biUnion E ∩ L).card) ∧
  (∀ t ∈ W, ∀ a ∈ E t, a ∉ L → p a = b t) ∧
  ∀ a ∈ W.biUnion E ∩ L, ∃ t ∈ W, ∃ u ∈ W, a ∈ E t ∧ a ∈ E u ∧ b t ≠ b u

/-- A triangle with one free edge forces its color. Tracing a failure of this
assignment attaches the forcing triangle as a leaf of the certificate. -/
private theorem certificate_of_failure {ι α : Type*} [DecidableEq α] [DecidableEq ι]
    (E : ι → Finset α) (T : Finset ι) (L : Finset α) (p : α → Bool)
    (hsize : ∀ t ∈ T, (E t).card = 3)
    (hdeg : ∀ a ∈ L, (T.filter fun t => a ∈ E t).card ≤ 2)
    (fail : ¬ ∃ c : α → Bool, (∀ a ∉ L, c a = p a) ∧ ∀ t ∈ T, Mixed c (E t)) :
    ∃ W ⊆ T, ∃ b, Certificate E L p W b := by
  classical
  induction T using Finset.strongInduction generalizing L p with
  | H T ih =>
    obtain ⟨r,hr,hn,hfew⟩ : ∃ r ∈ T, ¬ Mixed p (E r \ L) ∧ (E r ∩ L).card < 2 := by
      by_contra! all
      exact fail (fill_unforced E T L p hsize hdeg all)
    have hpositive : (E r \ L).Nonempty := by
      have hc := card_sdiff_add_card_inter (E r) L
      have := hsize r hr
      exact card_pos.mp (by omega)
    obtain ⟨z,hz⟩ := hpositive
    have same (a) (ha : a ∈ E r \ L) : p a = p z :=
      Classical.not_not.mp (fun h => hn ⟨a,ha,z,hz,h⟩)
    by_cases hzero : E r ∩ L = ∅
    · refine ⟨{r}, singleton_subset_iff.mpr hr, fun _ => p z, ?_⟩
      refine ⟨by simp [hzero], ?_, ?_, by simp [hzero]⟩
      · intro B hB
        have := card_lt_card hB
        simp only [card_singleton] at this
        omega
      intro t ht a ha hout
      exact same a (mem_sdiff.mpr ⟨mem_singleton.mp ht ▸ ha,hout⟩)
    · obtain ⟨x,honly⟩ : ∃ x, E r ∩ L = {x} := by
        apply card_eq_one.mp
        have := card_pos.mpr (nonempty_iff_ne_empty.mpr hzero)
        omega
      have hx : x ∈ E r ∩ L := honly ▸ mem_singleton_self _
      let q := Function.update p x (!p z)
      have qx : q x = !p z := by simp [q]
      have qeq {a} (ha : a ≠ x) : q a = p a := Function.update_of_ne ha _ _
      have residual : ¬ ∃ c : α → Bool, (∀ a ∉ L.erase x, c a = q a) ∧
          ∀ t ∈ T.erase r, Mixed c (E t) := by
        rintro ⟨c,hc,hm⟩
        apply fail
        refine ⟨c,fun a ha => (hc _ (fun h => ha (mem_of_mem_erase h))).trans
          (qeq (fun e => ha (e ▸ (mem_inter.mp hx).2))), ?_⟩
        intro t ht
        by_cases h : t = r
        · subst t
          refine ⟨x,(mem_inter.mp hx).1,z,(mem_sdiff.mp hz).1,?_⟩
          have hzx : z ≠ x := fun e => (mem_sdiff.mp hz).2 (e ▸ (mem_inter.mp hx).2)
          rw [hc x (notMem_erase _ _),qx,hc z (fun h => (mem_sdiff.mp hz).2 (mem_of_mem_erase h)),qeq hzx]
          simp
        · exact hm t (mem_erase.mpr ⟨h,ht⟩)
      obtain ⟨W,hW,b,hw⟩ := ih (T.erase r) (erase_ssubset hr) (L.erase x) q
        (fun t ht => hsize t (mem_of_mem_erase ht))
        (fun a ha => (card_le_card (filter_subset_filter _ (erase_subset r T))).trans
          (hdeg a (mem_of_mem_erase ha))) residual
      obtain ⟨hcard,hminimal,hfixed,hop⟩ := hw
      have hrW : r ∉ W := fun h => (mem_erase.mp (hW h)).1 rfl
      have hWT := hW.trans (erase_subset r T)
      have old {t a} (ht : t ∈ W) (ha : a ∈ E t) (hout : a ∉ L) : p a = b t :=
        (qeq (show a ≠ x from fun e => hout (e ▸ (mem_inter.mp hx).2))).symm.trans
          (hfixed t ht a ha (fun h => hout (mem_of_mem_erase h)))
      by_cases htouch : x ∈ W.biUnion E
      · obtain ⟨u,hu,hxu⟩ := mem_biUnion.mp htouch
        let b' := Function.update b r (p z)
        have br : b' r = p z := by simp [b']
        have bw {t} (ht : t ∈ W) : b' t = b t :=
          Function.update_of_ne (show t ≠ r from fun e => hrW (e ▸ ht)) _ _
        have bu := hfixed u hu x hxu (notMem_erase _ _)
        have eqset : (insert r W).biUnion E ∩ L = insert x (W.biUnion E ∩ L.erase x) := by
          ext a
          by_cases h : a = x
          · subst a
            simp [biUnion_insert, (mem_inter.mp hx).1, (mem_inter.mp hx).2]
          · have hh : a ∈ E r → a ∉ L := fun ha hl => h (mem_singleton.mp
                (honly ▸ mem_inter.mpr ⟨ha,hl⟩ : a ∈ ({x} : Finset α)))
            simp only [biUnion_insert,mem_inter,mem_union,mem_insert,mem_erase]
            tauto
        refine ⟨insert r W,insert_subset hr hWT,b', ?_, attach_leaf E L W r x (mem_inter.mp hx).1 htouch (mem_inter.mp hx).2 hcard hminimal, ?_, ?_⟩
        · rw [eqset,card_insert_of_notMem (by simp),card_insert_of_notMem hrW]
          omega
        · intro t ht a ha hout
          rcases mem_insert.mp ht with rfl | ht
          · exact (same a (mem_sdiff.mpr ⟨ha,hout⟩)).trans br.symm
          · exact (old ht ha hout).trans (bw ht).symm
        · intro a ha
          rw [eqset] at ha
          rcases mem_insert.mp ha with rfl | ha
          · refine ⟨r,mem_insert_self _ _,u,mem_insert_of_mem hu,(mem_inter.mp hx).1,hxu,?_⟩
            rw [br,bw hu,← bu,qx]
            simp
          · obtain ⟨s,hs,t,ht,has,hat,hst⟩ := hop a ha
            exact ⟨s,mem_insert_of_mem hs,t,mem_insert_of_mem ht,has,hat,by rwa [bw hs,bw ht]⟩
      · have eqset : W.biUnion E ∩ L = W.biUnion E ∩ L.erase x := by
          ext a
          by_cases h : a = x
          · simp [h,htouch]
          · simp [h]
        exact ⟨W,hWT,b,eqset ▸ hcard,fun B hB => (hminimal B hB).trans
            (card_le_card (inter_subset_inter_left (erase_subset x L))),fun _ ht _ ha hout => old ht ha hout,
          fun a ha => hop a (eqset ▸ ha)⟩

private theorem certificate_blocks {ι α : Type*} [DecidableEq α] [DecidableEq ι]
    (E : ι → Finset α) (L : Finset α) (p : α → Bool) (W : Finset ι) (b : ι → Bool)
    (hdeg : ∀ a ∈ L, (W.filter fun t => a ∈ E t).card ≤ 2)
    (h : Certificate E L p W b) (c : α → Bool) (hc : ∀ a ∉ L, c a = p a) :
    ¬ ∀ t ∈ W, Mixed c (E t) := by
  classical
  intro hg
  obtain ⟨hcard,_,hfixed,hop⟩ := h
  let D := W.biUnion E ∩ L
  let R (t : ι) (a : α) := a ∈ E t ∧ c a ≠ b t
  have hl (t) (ht : t ∈ W) : 1 ≤ (D.bipartiteAbove R t).card := by
    obtain ⟨x,hx,y,hy,hdiff⟩ := hg t ht
    obtain ⟨a,ha,hab⟩ : ∃ a ∈ E t, c a ≠ b t := by
      by_contra! hn
      exact hdiff ((hn x hx).trans (hn y hy).symm)
    have haL : a ∈ L := by
      by_contra hn
      exact hab ((hc a hn).trans (hfixed t ht a ha hn))
    exact card_pos.mpr ⟨a,mem_filter.mpr
      ⟨mem_inter.mpr ⟨mem_biUnion.mpr ⟨t,ht,ha⟩,haL⟩,ha,hab⟩⟩
  have hr (a) (ha : a ∈ D) : (W.bipartiteBelow R a).card ≤ 1 := by
    obtain ⟨s,hs,t,ht,has,hat,hst⟩ := hop a ha
    obtain ⟨u,hu,hau,he⟩ : ∃ u ∈ W, a ∈ E u ∧ c a = b u := by
      by_cases eq : c a = b s
      · exact ⟨s,hs,has,eq⟩
      · exact ⟨t,ht,hat,by cases hb : b s <;> cases hb' : b t <;> cases hh : c a <;> simp_all⟩
    have hu' : u ∉ W.bipartiteBelow R a := fun h => (mem_filter.mp h).2.2 he
    have hsub : insert u (W.bipartiteBelow R a) ⊆ W.filter (fun t => a ∈ E t) := by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact mem_filter.mpr ⟨hu,hau⟩
      · exact mem_filter.mpr ⟨(mem_filter.mp hv).1,(mem_filter.mp hv).2.1⟩
    have hbound := (card_le_card hsub).trans (hdeg a (mem_inter.mp ha).2)
    rw [card_insert_of_notMem hu'] at hbound
    omega
  have count := card_nsmul_le_card_nsmul R hl hr
  change W.card * 1 ≤ D.card * 1 at count
  change D.card + 1 = W.card at hcard
  omega

private theorem two_forced_leaves {ι α : Type*} [DecidableEq α] [DecidableEq ι]
    (E : ι → Finset α) (L : Finset α) (W : Finset ι)
    (hdeg : ∀ a ∈ L, (W.filter fun t => a ∈ E t).card ≤ 2)
    (hcard : (W.biUnion E ∩ L).card + 1 = W.card)
    (hpos : ∀ t ∈ W, (E t ∩ L).Nonempty) :
    2 ≤ (W.filter fun t => (E t ∩ L).card = 1).card := by
  classical
  let D := W.biUnion E ∩ L
  let leaves := W.filter fun t => (E t ∩ L).card = 1
  let R (t : ι) (x : α) := x ∈ E t
  have eqD (t) (ht : t ∈ W) : D.bipartiteAbove R t = E t ∩ L := by
    ext x
    constructor
    · intro hx
      exact mem_inter.mpr ⟨(mem_filter.mp hx).2,(mem_inter.mp (mem_filter.mp hx).1).2⟩
    · intro hx
      have := mem_inter.mp hx
      exact mem_filter.mpr ⟨mem_inter.mpr ⟨mem_biUnion.mpr ⟨t,ht,this.1⟩,this.2⟩,this.1⟩
  have h1 : W.card * 2 ≤ (∑ t ∈ W, (D.bipartiteAbove R t).card) + leaves.card := by
    have hsum := Finset.sum_le_sum (s := W) (f := fun _ => 2)
      (g := fun t => (D.bipartiteAbove R t).card + if (E t ∩ L).card = 1 then 1 else 0)
      (fun t ht => by
        rw [eqD t ht]
        have := card_pos.mpr (hpos t ht)
        split <;> omega)
    simpa only [Finset.sum_add_distrib, sum_const, smul_eq_mul, sum_boole, Nat.cast_id, leaves] using hsum
  have h2 : (∑ x ∈ D, (W.bipartiteBelow R x).card) ≤ D.card * 2 := by
    simpa using Finset.sum_le_sum (s := D) (f := fun x => (W.bipartiteBelow R x).card) (g := fun _ => 2)
      (fun x hx => hdeg x (mem_inter.mp hx).2)
  rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R] at h1
  change D.card + 1 = W.card at hcard
  change 2 ≤ leaves.card
  omega


-- The triangle edge calculation and transversal argument are adapted from the merged R2.
private theorem three_edge_set {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {a b c : Fin n}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    ({a,b,c} : Finset (Fin n)).sym2 ∩ G.edgeFinset =
      ({s(a,b),s(a,c),s(b,c)} : Finset (Sym2 (Fin n))) := by
  apply Subset.antisymm
  · simp only [subset_iff,Sym2.forall,mem_inter,mk_mem_sym2_iff,mem_insert,
      mem_edgeFinset,mem_singleton,mem_edgeSet,and_imp]
    rintro d e (rfl|rfl|rfl) (rfl|rfl|rfl) h <;> simp [*] at *
  · simp [insert_subset,mem_inter,mem_edgeFinset,hab,hac,hbc]

private theorem H_attained {n : ℕ} (F : SimpleGraph (Fin n)) (hF : F.CliqueFree 3) :
    ∃ s, F.IsNIndepSet (Erdos151.H n) s := by
  let sizes : Set ℕ :=
    {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s}
  have hnonempty : sizes.Nonempty := by
    refine ⟨0, ?_⟩
    intro G _
    exact ⟨∅,by simp [SimpleGraph.isNIndepSet_iff]⟩
  have hfinite : sizes.Finite := by
    refine (Set.finite_Iic n).subset ?_
    intro k hk
    obtain ⟨s,hs⟩ := hk F hF
    simpa [hs.card_eq] using Finset.card_le_univ s
  have hmem : Erdos151.H n ∈ sizes := hnonempty.csSup_mem hfinite
  exact hmem F hF

private theorem transversal_of_edge_coloring {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → Fin n → Bool) (hs : ∀ x y, c x y = c y x)
    (hc : ∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
      ∀ b, ¬ (c x y = b ∧ c x z = b ∧ c y z = b)) :
    cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  let F : SimpleGraph (Fin n) := {
    Adj := fun x y => G.Adj x y ∧ (c x y = true ∨ ¬ ∃ w, G.Adj x w ∧ G.Adj y w)
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.elim (fun h => Or.inl ((hs _ _).trans h))
      (fun h => Or.inr (fun ⟨w,hw,hw'⟩ => h ⟨w,hw',hw⟩))⟩⟩
    loopless := ⟨fun _ h => G.irrefl h.1⟩ }
  have hF : F.CliqueFree 3 := by
    intro t h
    obtain ⟨x,y,z,hxy,hxz,hyz,-⟩ := is3Clique_iff.mp h
    exact hc x y z hxy.1 hxz.1 hyz.1 true
      ⟨hxy.2.resolve_right (fun h => h ⟨z,hxz.1,hyz.1⟩),
        hxz.2.resolve_right (fun h => h ⟨y,hxy.1,hyz.1.symm⟩),
        hyz.2.resolve_right (fun h => h ⟨x,hxy.1.symm,hxz.1.symm⟩)⟩
  obtain ⟨I,hI⟩ := H_attained F hF
  have hhit : G.IsCliqueTransversal Iᶜ := by
    intro t ht
    by_contra! h
    have hIn {x : Fin n} (hx : x ∈ t) : x ∈ I := by simpa using h x hx
    have hNo {x y : Fin n} (hx : x ∈ t) (hy : y ∈ t) (hxy : G.Adj x y) :
        c x y = false := by
      cases hb : c x y
      · rfl
      · exact (hI.isIndepSet (hIn hx) (hIn hy) hxy.ne ⟨hxy,Or.inl hb⟩).elim
    have hNotThree : t.card < 3 := by
      by_contra! hLarge
      obtain ⟨u,hu,huC⟩ := exists_subset_card_eq hLarge
      have hClique : G.IsNClique 3 u :=
        ⟨fun _ hx _ hy hxy => ht.1.1 (hu hx) (hu hy) hxy,huC⟩
      obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := is3Clique_iff.mp hClique
      have hx : x ∈ t := hu (by simp)
      have hy : y ∈ t := hu (by simp)
      have hz : z ∈ t := hu (by simp)
      exact hc x y z hxy hxz hyz false ⟨hNo hx hy hxy,hNo hx hz hxz,hNo hy hz hyz⟩
    have hTwo : t.card = 2 := by have := ht.2; omega
    obtain ⟨x,y,hxy,htxy⟩ := card_eq_two.mp hTwo
    have hx : x ∈ t := by simp [htxy]
    have hy : y ∈ t := by simp [htxy]
    have hAdj := ht.1.1 hx hy hxy
    have hN : ¬ ∃ w, G.Adj x w ∧ G.Adj y w := by
      rintro ⟨w,hwx,hwy⟩
      have hSub : G.IsClique (↑(insert w t) : Set (Fin n)) := by
        rw [coe_insert]
        apply ht.1.1.insert
        intro u hu _
        have : u = x ∨ u = y := by simpa [htxy] using hu
        exact this.elim (fun h => h ▸ hwx.symm) (fun h => h ▸ hwy.symm)
      have hwMem : w ∈ t := ht.1.2 hSub (subset_insert _ _) (mem_insert_self _ _)
      have : w = x ∨ w = y := by simpa [htxy] using hwMem
      exact this.elim hwx.ne.symm hwy.ne.symm
    exact hI.isIndepSet (hIn hx) (hIn hy) hxy ⟨hAdj,Or.inr hN⟩
  apply csInf_le'
  exact ⟨Iᶜ,hhit,by rw [card_compl,Fintype.card_fin,hI.card_eq]⟩




/-- Any set of edges meeting each affected triangle at least twice must reach
the boundary of a certificate. -/
private theorem reaches_boundary {ι α : Type*} [DecidableEq α] [DecidableEq ι]
    (E : ι → Finset α) (L : Finset α) (W : Finset ι) (p : α → Bool) (b : ι → Bool)
    (hc : Certificate E L p W b) (D : Finset α)
    (hdeg : ∀ a ∈ L, (W.filter fun t => a ∈ E t).card ≤ 2)
    (hD : ∀ t ∈ W, (E t ∩ D).Nonempty → 2 ≤ (E t ∩ D).card)
    (htouch : (W.biUnion E ∩ D).Nonempty) :
    ∃ a ∈ W.biUnion E ∩ D, a ∉ L := by
  classical
  by_contra! hin
  let A := W.filter fun t => (E t ∩ D).Nonempty
  let B := W \ A
  let P := W.biUnion E ∩ D
  obtain ⟨a,ha⟩ := htouch
  obtain ⟨t,ht,hat⟩ := mem_biUnion.mp (mem_inter.mp ha).1
  have htA : t ∈ A := mem_filter.mpr ⟨ht,a,mem_inter.mpr ⟨hat,(mem_inter.mp ha).2⟩⟩
  have hB : B ⊂ W := Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,fun he =>
    (mem_sdiff.mp (show t ∈ B from he ▸ ht)).2 htA⟩
  have hAP : A.card ≤ P.card := by
    have hl (s) (hs : s ∈ A) : 2 ≤ (P.bipartiteAbove (fun u e => e ∈ E u) s).card := by
      apply (hD s (mem_filter.mp hs).1 (mem_filter.mp hs).2).trans
      apply card_le_card
      intro e he
      exact mem_filter.mpr ⟨mem_inter.mpr ⟨mem_biUnion.mpr
        ⟨s,(mem_filter.mp hs).1,(mem_inter.mp he).1⟩,(mem_inter.mp he).2⟩,(mem_inter.mp he).1⟩
    have hr (a) (ha : a ∈ P) : (A.bipartiteBelow (fun t e => e ∈ E t) a).card ≤ 2 :=
      (card_le_card (filter_subset_filter _ (filter_subset _ _ : A ⊆ W))).trans (hdeg a (hin a ha))
    have count := card_nsmul_le_card_nsmul (fun t e => e ∈ E t) hl hr
    change A.card * 2 ≤ P.card * 2 at count
    omega
  have dis : Disjoint P (B.biUnion E ∩ L) := by
    apply Finset.disjoint_left.mpr
    intro e hep heb
    obtain ⟨s,hs,hes⟩ := mem_biUnion.mp (mem_inter.mp heb).1
    exact (mem_sdiff.mp hs).2 (mem_filter.mpr ⟨(mem_sdiff.mp hs).1,
      e,mem_inter.mpr ⟨hes,(mem_inter.mp hep).2⟩⟩)
  have sub : P ∪ (B.biUnion E ∩ L) ⊆ W.biUnion E ∩ L := by
    apply union_subset
    · exact fun e he => mem_inter.mpr ⟨(mem_inter.mp he).1,hin e he⟩
    · intro e he
      obtain ⟨s,hs,hes⟩ := mem_biUnion.mp (mem_inter.mp he).1
      exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨s,hB.le hs,hes⟩,(mem_inter.mp he).2⟩
  have hbound := card_le_card sub
  rw [card_union_of_disjoint dis] at hbound
  have hpart : B.card + A.card = W.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have := hc.2.1 B hB
  have := hc.1
  omega

private theorem blocked_tree_spans {n : ℕ} (G : SimpleGraph (Fin n))
    (T W : Finset (Finset (Fin n))) (L : Finset (Sym2 (Fin n)))
    (p : Sym2 (Fin n) → Bool) (b : Finset (Fin n) → Bool)
    (hT : T ⊆ G.cliqueFinset 3) (hW : W ⊆ T)
    (hc : Certificate (fun t => t.sym2 ∩ G.edgeFinset) L p W b)
    (hdeg : ∀ a ∈ L, (T.filter fun t => a ∈ t.sym2 ∩ G.edgeFinset).card ≤ 2)
    (s : Fin n → Bool)
    (hs : ∃ t ∈ W, ∃ x ∈ t, ∃ y ∈ t, s x ≠ s y) :
    ∃ t ∈ W, ∃ x ∈ t, ∃ y ∈ t, s x ≠ s y ∧ s(x,y) ∉ L := by
  classical
  let cross : Sym2 (Fin n) → Prop := Sym2.lift ⟨fun x y => s x ≠ s y,
    fun x y => propext ne_comm⟩
  let D := univ.filter cross
  let E (t : Finset (Fin n)) := t.sym2 ∩ G.edgeFinset
  have cut (x y : Fin n) : s(x,y) ∈ D ↔ s x ≠ s y := by
    simp [D,cross]
  have edge {t} (ht : t ∈ W) {x y} (hx : x ∈ t) (hy : y ∈ t) (hxy : s x ≠ s y) :
      s(x,y) ∈ E t := by
    have ne : x ≠ y := fun he => hxy (congrArg s he)
    exact mem_inter.mpr ⟨mk_mem_sym2_iff.mpr ⟨hx,hy⟩,mem_edgeFinset.mpr
      ((mem_cliqueFinset_iff.mp (hT (hW ht))).isClique hx hy ne)⟩
  have lift_cut (t : Finset (Fin n)) (ht : t ∈ W) (hne : (E t ∩ D).Nonempty) :
      2 ≤ (E t ∩ D).card := by
    obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := is3Clique_iff.mp (mem_cliqueFinset_iff.mp (hT (hW ht)))
    have he : E {x,y,z} = {s(x,y),s(x,z),s(y,z)} := three_edge_set G hxy hxz hyz
    rw [he] at hne ⊢
    have exy : s(x,y) ≠ s(x,z) := by simp [hyz.ne,hxz.ne]
    have exz : s(x,y) ≠ s(y,z) := by simp [hxy.ne,hxz.ne,hyz.ne]
    have eyz : s(x,z) ≠ s(y,z) := by simp [hxy.ne,hxz.ne]
    cases cx : s x <;> cases cy : s y <;> cases cz : s z <;>
      simp [insert_inter_of_mem, insert_inter_of_notMem, cut, cx, cy, cz, exy, exz, eyz] at hne ⊢
  obtain ⟨t,ht,x,hx,y,hy,hxy⟩ := hs
  have touch : (W.biUnion E ∩ D).Nonempty := ⟨s(x,y),mem_inter.mpr
    ⟨mem_biUnion.mpr ⟨t,ht,edge ht hx hy hxy⟩,(cut x y).mpr hxy⟩⟩
  obtain ⟨e,he,heL⟩ := reaches_boundary E L W p b hc D (fun a ha =>
    (card_le_card (filter_subset_filter _ hW)).trans (hdeg a ha)) lift_cut touch
  obtain ⟨t,ht,het⟩ := mem_biUnion.mp (mem_inter.mp he).1
  obtain ⟨⟨x,y⟩,rfl⟩ := Sym2.mk_surjective e
  obtain ⟨hx,hy⟩ := mk_mem_sym2_iff.mp (mem_inter.mp het).1
  exact ⟨t,ht,x,hx,y,hy,(cut x y).mp (mem_inter.mp he).2,heL⟩

private theorem triangle_size {n : ℕ} (G : SimpleGraph (Fin n)) (t : Finset (Fin n))
    (ht : t ∈ G.cliqueFinset 3) : (t.sym2 ∩ G.edgeFinset).card = 3 := by
  classical
  let E (u : Finset (Fin n)) := u.sym2 ∩ G.edgeFinset
  change (E t).card = 3
  obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := is3Clique_iff.mp (mem_cliqueFinset_iff.mp ht)
  rw [show E {x,y,z} = _ from three_edge_set G hxy hxz hyz]
  refine card_eq_three.mpr ⟨_,_,_,?_,?_,?_,rfl⟩ <;> simp [hxy.ne,hxz.ne,hyz.ne]

private theorem bound_of_coloring {n : ℕ} (G : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → Bool)
    (hc : ∀ t ∈ G.cliqueFinset 3, Mixed c (t.sym2 ∩ G.edgeFinset)) :
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  classical
  let E (u : Finset (Fin n)) := u.sym2 ∩ G.edgeFinset
  apply transversal_of_edge_coloring G (fun x y => c s(x,y))
    (fun x y => congrArg c Sym2.eq_swap)
  intro x y z hxy hxz hyz b hmono
  have hm := hc {x,y,z} (mem_cliqueFinset_iff.mpr (is3Clique_triple_iff.mpr ⟨hxy,hxz,hyz⟩))
  have he : E {x,y,z} = {s(x,y),s(x,z),s(y,z)} := three_edge_set G hxy hxz hyz
  obtain ⟨i,hi,j,hj,hn⟩ := hm
  have const (a) (ha : a ∈ E {x,y,z}) : c a = b := by
    rw [he] at ha
    simp only [mem_insert,mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hmono.1
    · exact hmono.2.1
    · exact hmono.2.2
  exact hn ((const i hi).trans (const j hj).symm)

/-- Precolor all but a set of edges of triangle multiplicity at most two. If
the completely colored triangles are bichromatic and at most one triangle has
a unique free edge with its other two edges the same color, the transversal
bound follows at every order. -/
private theorem bound_of_partial_coloring {n : ℕ} (G : SimpleGraph (Fin n))
    (L : Finset (Sym2 (Fin n))) (p : Sym2 (Fin n) → Bool) :
    let T := G.cliqueFinset 3
    let E (t : Finset (Fin n)) := t.sym2 ∩ G.edgeFinset
    (∀ e ∈ L, (T.filter fun t => e ∈ E t).card ≤ 2) →
    (∀ t ∈ T, E t ∩ L = ∅ → Mixed p (E t)) →
    (T.filter fun t => (E t ∩ L).card = 1 ∧ ¬ Mixed p (E t \ L)).card ≤ 1 →
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  classical
  dsimp only
  intro hd hg hf
  let T := G.cliqueFinset 3
  let E (t : Finset (Fin n)) := t.sym2 ∩ G.edgeFinset
  obtain ⟨c,_,hc⟩ : ∃ c : Sym2 (Fin n) → Bool, (∀ e ∉ L, c e = p e) ∧
      ∀ t ∈ T, Mixed c (E t) := by
    by_contra h
    obtain ⟨W,hWT,b,hw⟩ := certificate_of_failure E T L p (triangle_size G) hd h
    have hpos (t) (ht : t ∈ W) : (E t ∩ L).Nonempty := by
      by_contra! hem
      obtain ⟨a,ha,d,hd',hne⟩ := hg t (hWT ht) hem
      have fixed (e) (he : e ∈ E t) : p e = b t := hw.2.2.1 t ht e he
        (fun hel => notMem_empty _ (hem ▸ mem_inter.mpr ⟨he,hel⟩))
      exact hne ((fixed a ha).trans (fixed d hd').symm)
    have hleaves := two_forced_leaves E L W (fun a ha =>
      (card_le_card (filter_subset_filter _ hWT)).trans (hd a ha)) hw.1 hpos
    have sub : (W.filter fun t => (E t ∩ L).card = 1) ⊆
        T.filter (fun t => (E t ∩ L).card = 1 ∧ ¬ Mixed p (E t \ L)) := by
      intro t ht
      obtain ⟨hwT,hone⟩ := mem_filter.mp ht
      refine mem_filter.mpr ⟨hWT hwT,hone,?_⟩
      rintro ⟨a,ha,d,hd',had⟩
      have fixed (e) (he : e ∈ E t \ L) :=
        hw.2.2.1 t hwT e (mem_sdiff.mp he).1 (mem_sdiff.mp he).2
      exact had ((fixed a ha).trans (fixed d hd').symm)
    exact (by decide : ¬ 2 ≤ 1) (hleaves.trans ((card_le_card sub).trans hf))
  exact bound_of_coloring G c hc

/-- A minimal triangle Ramsey family with at least three occurrences of each of its edges. -/
def H1 : Prop :=
  ∀ n, 11 ≤ Erdos151.H n → ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H n) →
    let E (t : Finset (Fin n)) := t.sym2 ∩ G.edgeFinset
    let good (c : Sym2 (Fin n) → Bool) (t : Finset (Fin n)) :=
      ∃ a ∈ E t, ∃ b ∈ E t, c a ≠ c b
    ∀ T ⊆ G.cliqueFinset 3,
      (¬ ∃ c, ∀ t ∈ T, good c t) →
      (∀ r ∈ T, ∃ c, ∀ t ∈ T.erase r, good c t) →
      (∀ t ∈ T, ∀ e ∈ E t, 3 ≤ (T.filter fun u => e ∈ E u).card) →
      cliqueTransversalNumber G ≤ n - Erdos151.H n

/-- In the mixed case each row is in a closed light-edge tree. Every coloring
of the heavy edges that works on the all-heavy triangles is blocked on a tree
with at least two one-light-edge triangles. -/
def H2 : Prop :=
  ∀ n, 11 ≤ Erdos151.H n → ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H n) →
    (∃ x y, G.Adj x y ∧ 3 ≤ (univ.filter fun z => G.Adj x z ∧ G.Adj y z).card) →
    let E (t : Finset (Fin n)) := t.sym2 ∩ G.edgeFinset
    ∀ T ⊆ G.cliqueFinset 3,
      let L := G.edgeFinset.filter fun e => (T.filter fun t => e ∈ E t).card ≤ 2
      let good (p : Sym2 (Fin n) → Bool) := ∀ t ∈ T, E t ∩ L = ∅ →
        ∃ a ∈ E t, ∃ b ∈ E t, p a ≠ p b
      let tree (p : Sym2 (Fin n) → Bool) (W : Finset (Finset (Fin n))) :=
        ∃ b : Finset (Fin n) → Bool,
          (W.biUnion E ∩ L).card + 1 = W.card ∧
          (∀ B ⊂ W, B.card ≤ (B.biUnion E ∩ L).card) ∧
          (∀ t ∈ W, ∀ e ∈ E t, e ∉ L → p e = b t) ∧
          (∀ e ∈ W.biUnion E ∩ L, ∃ t ∈ W, ∃ u ∈ W, e ∈ E t ∧ e ∈ E u ∧ b t ≠ b u) ∧
          ∀ s : Fin n → Bool, (∃ t ∈ W, ∃ x ∈ t, ∃ y ∈ t, s x ≠ s y) →
            ∃ t ∈ W, ∃ x ∈ t, ∃ y ∈ t, s x ≠ s y ∧ s(x,y) ∉ L
      (∃ p, good p) →
      (∀ r ∈ T, ∃ p W, W ⊆ T ∧ r ∈ W ∧ tree p W) →
      (∀ p, good p → ∃ W ⊆ T, tree p W ∧ 2 ≤ (W.filter fun t => (E t ∩ L).card = 1).card) →
      cliqueTransversalNumber G ≤ n - Erdos151.H n

theorem main : H1 → H2 → OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R1.H2 := by
  classical
  intro h1 h2 n hk G h4 hdeg hbook
  let E (t : Finset (Fin n)) := t.sym2 ∩ G.edgeFinset
  let fails (T : Finset (Finset (Fin n))) := ¬ ∃ c, ∀ t ∈ T, Mixed c (E t)
  by_cases hfail : fails (G.cliqueFinset 3)
  swap
  · obtain ⟨c,hc⟩ : ∃ c, ∀ t ∈ G.cliqueFinset 3, Mixed c (E t) := Classical.not_not.mp hfail
    apply bound_of_partial_coloring G ∅ c
    · simp
    · exact fun t ht _ => hc t ht
    · simp
  obtain ⟨T,hTG,hmin⟩ := exists_minimal_le_of_wellFoundedLT fails (G.cliqueFinset 3) hfail
  have proper {B : Finset (Finset (Fin n))} (hB : B ⊂ T) :
      ∃ c, ∀ t ∈ B, Mixed c (E t) := by
    by_contra h
    exact hB.not_ge (hmin.2 h hB.le)
  let L := G.edgeFinset.filter fun e => (T.filter fun t => e ∈ E t).card ≤ 2
  let U := T.filter fun t => E t ∩ L = ∅
  by_cases heq : U = T
  · apply h1 n hk G h4 hdeg T hTG hmin.1 (fun r hr => proper (erase_ssubset hr))
    intro t ht e he
    by_contra! h
    have small : (T.filter fun u => e ∈ E u).card < 3 := h
    have hel : e ∈ L := mem_filter.mpr ⟨(mem_inter.mp he).2,by omega⟩
    have htU : t ∈ U := heq ▸ ht
    exact (Finset.notMem_empty e) ((mem_filter.mp htU).2 ▸ mem_inter.mpr ⟨he,hel⟩)
  have sizes (t) (ht : t ∈ T) := triangle_size G t (hTG ht)
  have light (a) (ha : a ∈ L) : (T.filter fun t => a ∈ E t).card ≤ 2 :=
    (mem_filter.mp ha).2
  have witness (p : Sym2 (Fin n) → Bool) :=
    certificate_of_failure E T L p sizes light
      (fun ⟨c,_,hc⟩ => hmin.1 ⟨c,hc⟩)
  have span {q W b} (hWT : W ⊆ T) (hw : Certificate E L q W b) :=
    blocked_tree_spans G T W L q b hTG hWT hw light
  obtain ⟨p,hp⟩ := proper (Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _,heq⟩ : U ⊂ T)
  apply h2 n hk G h4 hdeg hbook T hTG
  · exact ⟨p,fun t ht he => hp t (mem_filter.mpr ⟨ht,he⟩)⟩
  · intro r hr
    obtain ⟨q,hq⟩ := proper (erase_ssubset hr)
    obtain ⟨W,hWT,b,hw⟩ := witness q
    refine ⟨q,W,hWT,?_,b,hw.1,hw.2.1,hw.2.2.1,hw.2.2.2,span hWT hw⟩
    by_contra hout
    apply certificate_blocks E L q W b (fun a ha =>
      (card_le_card (filter_subset_filter _ hWT)).trans (light a ha)) hw q (fun _ _ => rfl)
    exact fun t ht => hq t (mem_erase.mpr ⟨fun e => hout (e ▸ ht),hWT ht⟩)
  · intro q hq
    obtain ⟨W,hWT,b,hw⟩ := witness q
    refine ⟨W,hWT,⟨b,hw.1,hw.2.1,hw.2.2.1,hw.2.2.2,span hWT hw⟩,two_forced_leaves E L W (fun a ha =>
      (card_le_card (filter_subset_filter _ hWT)).trans (light a ha)) hw.1 ?_⟩
    intro t ht
    by_contra! hempty
    have hem : E t ∩ L = ∅ := by simpa using hempty
    obtain ⟨a,ha,a',ha',hne⟩ := hq t (hWT ht) hem
    have fixed (e) (he : e ∈ E t) : q e = b t := by
      apply hw.2.2.1 t ht e he
      intro hel
      exact notMem_empty _ (hem ▸ mem_inter.mpr ⟨he,hel⟩)
    exact hne ((fixed a ha).trans (fixed a' ha').symm)

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R1_H2_R1
