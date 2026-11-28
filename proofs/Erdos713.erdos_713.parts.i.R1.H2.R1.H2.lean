import OMAReductions.R_Erdos713_erdos_713_parts_i_R1_H2_R1

/-!
For a forbidden star forest on q vertices, choose one center per star.
In a free host, set aside the h vertices of degree at least q. In the
remaining bounded-degree graph, take the largest d for which sufficiently
many vertices have degree at least d. Stars of degree at most d fit greedily
in disjoint closed neighborhoods. If there were at most h larger stars,
their centers could be assigned to the reserved vertices and their leaves
embedded last. Thus more than h forbidden stars have degree greater than d.
Counting degrees bounds twice the number of host edges by (2h+d)n+O_q(1).

Conversely, take h vertices adjacent to every vertex of a disjoint union
of cliques of size d+1. Each large forbidden star would have to use one
of those h vertices. Isolated vertices fill the remainder at bounded cost.
Maximizing over the finitely many admissible pairs (h,d) gives matching
bounds up to a constant. This formalizes the leading-order star-forest
result of Lidický, Liu and Palmer, *On the Turán Number of Forests*,
Electronic Journal of Combinatorics 20 (2013), P62, doi:10.37236/3142.
-/

-- Credit: @zarnab222-dev

open Finset SimpleGraph
open scoped Classical
namespace E713Stars


theorem extend_leaves {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (X : SimpleGraph W) (S : Finset V) (label : V → W)
    (inj : Set.InjOn label (S : Set V))
    (good : ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → X.Adj (label u) (label v))
    (leaves : ∀ v ∉ S, ∃ c ∈ S, (∀ w, G.Adj v w → w=c) ∧ Fintype.card V-1 ≤ X.degree (label c)) :
    G.IsContained X := by
  classical
  induction h : (univ \ S).card using Nat.strong_induction_on generalizing S label with
  | h k induct =>
    by_cases full : S=univ
    · have all (v : V) : v ∈ S := full ▸ mem_univ v
      exact ⟨⟨⟨label,fun ha => good _ (all _) _ (all _) ha⟩,fun _ _ eq => inj (all _) (all _) eq⟩⟩
    obtain ⟨v,hv⟩ : ∃ v, v ∉ S := by
      by_contra! all
      exact full (eq_univ_iff_forall.mpr all)
    obtain ⟨c,hc,parent,degree⟩ := leaves v hv
    let used := (S.erase c).image label
    have ssmall : S.card < Fintype.card V := by
      have := card_lt_card (ssubset_univ_iff.mpr full)
      simpa using this
    have cost : used.card < X.degree (label c) := by
      have u := card_image_le (s := S.erase c) (f := label)
      have rem := card_erase_add_one hc
      change ((S.erase c).image label).card < _
      omega
    obtain ⟨y,hy,fresh⟩ := exists_mem_notMem_of_card_lt_card (show used.card < (X.neighborFinset (label c)).card by simpa using cost)
    have cy := (X.mem_neighborFinset _ _).mp hy
    have outside (w : V) (hw : w ∈ S) : y ≠ label w := by
      by_cases eq : w=c
      · subst w; exact cy.ne.symm
      · exact fun e => fresh (e ▸ mem_image_of_mem label (mem_erase.mpr ⟨eq,hw⟩))
    let f := Function.update label v y
    have agree (w : V) (hw : w ∈ S) : f w=label w := by
      have ne : w ≠ v := fun e => hv (e ▸ hw)
      exact Function.update_of_ne ne ..
    have fv : f v=y := Function.update_self ..
    let T := insert v S
    have dec : (univ \ T).card < k := by
      rw [← h,card_sdiff_of_subset (subset_univ _),card_sdiff_of_subset (subset_univ _),
        show T=insert v S from rfl,card_insert_of_notMem hv,card_univ]
      omega
    apply induct _ dec T f
    · intro a ha b hb eq
      rcases mem_insert.mp ha with av | aa <;> rcases mem_insert.mp hb with bv | bb
      · exact av.trans bv.symm
      · rw [av,fv,agree _ bb] at eq; exact (outside _ bb eq).elim
      · rw [bv,fv,agree _ aa] at eq; exact (outside _ aa eq.symm).elim
      · rw [agree _ aa,agree _ bb] at eq; exact inj aa bb eq
    · intro a ha b hb ab
      rcases mem_insert.mp ha with av | aa <;> rcases mem_insert.mp hb with bv | bb
      · exact (ab.ne (av.trans bv.symm)).elim
      · rw [av] at ab ⊢; rw [fv,agree _ bb,parent _ ab]; exact cy.symm
      · rw [bv] at ab ⊢; rw [agree _ aa,fv,parent _ ab.symm]; exact cy
      · rw [agree _ aa,agree _ bb]; exact good _ aa _ bb ab
    · intro a ha
      obtain ⟨p,hp,unique,deg⟩ := leaves a (fun mem => ha (mem_insert_of_mem mem))
      exact ⟨p,mem_insert_of_mem hp,unique,(agree p hp).symm ▸ deg⟩
    · rfl

theorem embed_from_pools {V W : Type*} [Fintype V] [Fintype W] [Nonempty W]
    (G : SimpleGraph V) (X : SimpleGraph W) (C : Finset V)
    (ind : ∀ a ∈ C, ∀ b ∈ C, ¬G.Adj a b)
    (leaf : ∀ v ∉ C, ∃ c ∈ C, G.Adj v c ∧ ∀ w, G.Adj v w → w=c)
    (f : C ↪ W) (small : C → Prop) (P : C → Finset W)
    (pool_size : ∀ c, small c → G.degree c.val ≤ (P c).card)
    (pool_adj : ∀ c, ∀ w ∈ P c, X.Adj (f c) w)
    (no_center : ∀ c c', f c' ∉ P c)
    (apart : ∀ c c', c ≠ c' → Disjoint (P c) (P c'))
    (abundant : ∀ c, ¬small c → Fintype.card V-1 ≤ X.degree (f c)) : G.IsContained X := by
  classical
  have neighbor (v : V) (hv : v ∉ C) : ∃ c : C, G.Adj v c.val ∧ ∀ w, G.Adj v w → w=c.val := by
    obtain ⟨u,hu,h,uniq⟩ := leaf v hv
    exact ⟨⟨u,hu⟩,h,uniq⟩
  choose p edge uniq using neighbor
  have embeds (c : C) (sc : small c) : Nonempty ((G.neighborFinset c.val) ↪ (P c)) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Fintype.card_coe,G.card_neighborFinset_eq_degree] using pool_size c sc
  let g (c : C) (sc : small c) := (embeds c sc).some
  have local_inj {c b : C} (sc : small c) (sb : small b) (eq : c=b)
      (x : G.neighborFinset c.val) (y : G.neighborFinset b.val)
      (same : (g c sc x).val=(g b sb y).val) : x.val=y.val := by
    subst b
    exact congrArg Subtype.val ((g c sc).injective (Subtype.ext same))
  let label (v : V) : W := if h : v ∈ C then f ⟨v,h⟩ else
    if sc : small (p v h) then (g _ sc ⟨v,(G.mem_neighborFinset _ _).mpr (edge v h).symm⟩).val
    else Classical.choice ‹Nonempty W›
  let S := univ.filter fun v => ∀ h : v ∉ C, small (p v h)
  have centerLabel (v : V) (hv : v ∈ C) : label v=f ⟨v,hv⟩ := by simp [label,hv]
  have inS (c : C) : c.val ∈ S := mem_filter.mpr ⟨mem_univ _,fun h => (h c.property).elim⟩
  have smallLabel (v : V) (hv : v ∉ C) (hs : v ∈ S) : label v ∈ P (p v hv) := by
    have sc := (mem_filter.mp hs).2 hv
    simp only [label,hv,sc,↓reduceDIte]
    exact Subtype.property _
  apply extend_leaves G X S label
  · intro a ha b hb eq
    by_cases ac : a ∈ C <;> by_cases bc : b ∈ C
    · rw [centerLabel a ac,centerLabel b bc] at eq
      exact congrArg Subtype.val (f.injective eq)
    · have nb := smallLabel b bc hb
      rw [← eq,centerLabel a ac] at nb
      exact (no_center _ _ nb).elim
    · have na := smallLabel a ac ha
      rw [eq,centerLabel b bc] at na
      exact (no_center _ _ na).elim
    · have same : p a ac = p b bc := by
        by_contra ne
        exact disjoint_left.mp (apart _ _ ne) (smallLabel a ac ha) (eq.symm ▸ smallLabel b bc hb)
      have sa := (mem_filter.mp ha).2 ac
      have sb := (mem_filter.mp hb).2 bc
      simp only [label,ac,bc,sa,sb,↓reduceDIte] at eq
      exact local_inj sa sb same _ _ eq
  · intro a ha b hb ab
    by_cases ac : a ∈ C
    · have bc : b ∉ C := fun h => ind a ac b h ab
      have same : (⟨a,ac⟩ : C) = p b bc := Subtype.ext (uniq b bc a ab.symm)
      rw [centerLabel a ac,same]
      exact pool_adj _ _ (smallLabel b bc hb)
    · have bEq := uniq a ac b ab
      have bc := bEq.symm ▸ (p a ac).property
      have same : (⟨b,bc⟩ : C) = p a ac := Subtype.ext bEq
      rw [centerLabel b bc,same]
      exact (pool_adj _ _ (smallLabel a ac ha)).symm
  · intro v hv
    have vc : v ∉ C := fun h => hv (inS ⟨v,h⟩)
    have large : ¬small (p v vc) := fun sc => hv (mem_filter.mpr ⟨mem_univ _,fun _ => sc⟩)
    exact ⟨_,inS _,uniq v vc,by rw [centerLabel _ (p v vc).property]; exact abundant _ large⟩


theorem pack_sets {V : Type*} [DecidableEq V] (H : Finset V) (N : V → Finset V)
    (B k : ℕ) (pos : 0<B) (enough : k*B ≤ H.card)
    (cost : ∀ v ∈ H, (H.filter fun u => ¬ Disjoint (N u) (N v)).card ≤ B)
    (self : ∀ v ∈ H, v ∈ N v) :
    ∃ S ⊆ H, S.card=k ∧ (S : Set V).PairwiseDisjoint N := by
  classical
  induction k with
  | zero => exact ⟨∅,empty_subset _,rfl,by simp⟩
  | succ k ih =>
    obtain ⟨S,sub,sz,sep⟩ := ih ((Nat.mul_le_mul_right B (Nat.le_succ k)).trans enough)
    let bad := S.biUnion fun v => H.filter fun u => ¬Disjoint (N u) (N v)
    have limit : bad.card ≤ k*B := by
      calc bad.card ≤ _ := card_biUnion_le
           _ ≤ ∑ _ ∈ S, B := sum_le_sum (fun v hv => cost v (sub hv))
           _ = k*B := by simp [sz]
    have less : bad.card < H.card := by rw [Nat.succ_mul] at enough; omega
    obtain ⟨u,hu,hbad⟩ := exists_mem_notMem_of_card_lt_card less
    have apart (v) (hv : v ∈ S) : Disjoint (N u) (N v) := by
      by_contra ne
      exact hbad (mem_biUnion.mpr ⟨v,hv,mem_filter.mpr ⟨hu,ne⟩⟩)
    have fresh : u ∉ S := by intro h; exact disjoint_left.mp (apart u h) (self u hu) (self u hu)
    refine ⟨insert u S,insert_subset hu sub,by rw [card_insert_of_notMem fresh,sz],?_⟩
    rw [coe_insert,Set.pairwiseDisjoint_insert_of_notMem (by simpa using fresh)]
    exact ⟨sep,apart⟩

theorem pack_stars {W : Type*} [Fintype W] (X : SimpleGraph W) (H : Finset W)
    (D k : ℕ) (bound : ∀ v, X.degree v ≤ D) (enough : k*((D+1)*(D+1)) ≤ H.card) :
    ∃ S ⊆ H, S.card=k ∧ (S : Set W).PairwiseDisjoint (fun v => insert v (X.neighborFinset v)) := by
  classical
  let N (v : W) := insert v (X.neighborFinset v)
  have sz (v) : (N v).card ≤ D+1 := (card_insert_le ..).trans (by rw [X.card_neighborFinset_eq_degree]; exact Nat.add_le_add_right (bound v) 1)
  have symm {u v} (h : u ∈ N v) : v ∈ N u := by
    rcases mem_insert.mp h with rfl | h
    · exact mem_insert_self ..
    · exact mem_insert_of_mem ((X.mem_neighborFinset _ _).mpr ((X.mem_neighborFinset _ _).mp h).symm)
  apply pack_sets H N _ k (by positivity) enough _ (fun _ _ => mem_insert_self ..)
  intro v hv
  have sub : (H.filter fun u => ¬Disjoint (N u) (N v)) ⊆ (N v).biUnion N := by
    intro u hu
    obtain ⟨w,wu,wv⟩ := not_disjoint_iff.mp (mem_filter.mp hu).2
    exact mem_biUnion.mpr ⟨w,wv,symm wu⟩
  calc _ ≤ ((N v).biUnion N).card := card_le_card sub
       _ ≤ ∑ w ∈ N v, (N w).card := card_biUnion_le
       _ ≤ ∑ _ ∈ N v, (D+1) := sum_le_sum (fun w _ => sz w)
       _ ≤ _ := by simpa using Nat.mul_le_mul_right (D+1) (sz v)

theorem split_embedding {V W : Type*} [Fintype V] (p : V → Prop) (B S : Finset W) (apart : Disjoint B S)
    (left : (univ.filter p).card ≤ B.card) (right : (univ.filter fun v => ¬p v).card ≤ S.card) :
    ∃ f : V ↪ W, (∀ v, p v → f v ∈ B) ∧ (∀ v, ¬p v → f v ∈ S) := by
  classical
  let A := univ.filter p
  let T := univ.filter fun v => ¬p v
  let l : A ↪ B := (Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe] using left)).some
  let r : T ↪ S := (Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe] using right)).some
  let f (v : V) : W := if h : p v then (l ⟨v,mem_filter.mpr ⟨mem_univ _,h⟩⟩).val else (r ⟨v,mem_filter.mpr ⟨mem_univ _,h⟩⟩).val
  have inL (v) (h : p v) : f v ∈ B := by simp only [f,h,↓reduceDIte]; exact Subtype.property _
  have inR (v) (h : ¬p v) : f v ∈ S := by simp only [f,h,↓reduceDIte]; exact Subtype.property _
  refine ⟨⟨f,?_⟩,inL,inR⟩
  intro a b eq
  by_cases ha : p a <;> by_cases hb : p b
  · simp only [f,ha,hb,↓reduceDIte] at eq
    exact congrArg Subtype.val (l.injective (Subtype.ext eq))
  · exact (disjoint_left.mp apart (inL a ha) (eq.symm ▸ inR b hb)).elim
  · exact (disjoint_left.mp apart (inL b hb) (eq ▸ inR a ha)).elim
  · simp only [f,ha,hb,↓reduceDIte] at eq
    exact congrArg Subtype.val (r.injective (Subtype.ext eq))

theorem many_centers_embed {V W : Type*} [Fintype V] [Fintype W] [Nonempty W]
    (G : SimpleGraph V) (X Y : SimpleGraph W) (C : Finset V) (B : Finset W) (d D : ℕ)
    (ind : ∀ a ∈ C, ∀ b ∈ C, ¬G.Adj a b)
    (leaf : ∀ v ∉ C, ∃ c ∈ C, G.Adj v c ∧ ∀ w, G.Adj v w → w=c)
    (sub : Y ≤ X) (iso : ∀ b ∈ B, ∀ w, ¬Y.Adj b w)
    (ample : ∀ b ∈ B, Fintype.card V-1 ≤ X.degree b)
    (bounded : ∀ v, Y.degree v ≤ D)
    (hubs : (C.filter fun c => d < G.degree c).card ≤ B.card)
    (numerous : Fintype.card V*((D+1)*(D+1)) ≤ (univ.filter fun w => w ∉ B ∧ d ≤ Y.degree w).card) :
    G.IsContained X := by
  classical
  let H := univ.filter fun w => w ∉ B ∧ d ≤ Y.degree w
  let large (c : C) := d < G.degree c.val
  have hs : C.card*((D+1)*(D+1)) ≤ H.card := (Nat.mul_le_mul_right _ (card_le_univ C)).trans numerous
  obtain ⟨S,sh,size,sep⟩ := pack_stars Y H D C.card bounded hs
  have apart : Disjoint B S := disjoint_left.mpr fun w hw hS => (mem_filter.mp (sh hS)).2.1 hw
  have lc : (univ.filter large).card ≤ B.card := by
    let e := Function.Embedding.subtype (fun v => v ∈ C)
    have eq : (univ.filter large).map e=C.filter (fun c => d < G.degree c) := by ext; simp [e,large]; tauto
    rw [← eq,card_map] at hubs
    exact hubs
  obtain ⟨f,hi,lo⟩ := split_embedding large B S apart (by convert lc using 2; congr!) (by
    rw [size]
    exact (card_le_univ _).trans (le_of_eq (Fintype.card_coe C)))
  let P (c : C) := if large c then ∅ else Y.neighborFinset (f c)
  apply embed_from_pools G X C ind leaf f (fun c => ¬large c) P
  · intro c hc
    simp only [P,hc,if_false,Y.card_neighborFinset_eq_degree]
    exact (le_of_not_gt hc).trans (mem_filter.mp (sh (lo c hc))).2.2
  · intro c w hw
    by_cases hc : large c
    · simp [P,hc] at hw
    · exact sub ((Y.mem_neighborFinset _ _).mp (by simpa [P,hc] using hw))
  · intro c b hb
    by_cases hc : large c
    · simp [P,hc] at hb
    have edge := (Y.mem_neighborFinset (f c) (f b)).mp (by simpa [P,hc] using hb)
    by_cases bc : large b
    · exact iso _ (hi b bc) _ edge.symm
    by_cases eq : c=b
    · exact edge.ne (congrArg f eq)
    have ds := sep (lo c hc) (lo b bc) (fun e => eq (f.injective e))
    exact disjoint_left.mp ds (mem_insert_of_mem ((Y.mem_neighborFinset _ _).mpr edge)) (mem_insert_self ..)
  · intro c b ne
    by_cases hc : large c
    · simp [P,hc]
    by_cases hb : large b
    · simp [P,hb]
    have ds := sep (lo c hc) (lo b hb) (fun e => ne (f.injective e))
    simp only [P,hc,hb,if_false]
    exact ds.mono (subset_insert ..) (subset_insert ..)
  · intro c hn
    exact ample _ (hi c (not_not.mp hn))

theorem hub_cap {V W : Type*} [Fintype V] [Fintype W] [Nonempty W]
    (G : SimpleGraph V) (X : SimpleGraph W) (C : Finset V) (B : Finset W)
    (ind : ∀ a ∈ C, ∀ b ∈ C, ¬G.Adj a b)
    (leaf : ∀ v ∉ C, ∃ c ∈ C, G.Adj v c ∧ ∀ w, G.Adj v w → w=c)
    (ample : ∀ b ∈ B, Fintype.card V-1 ≤ X.degree b)
    (free : G.Free X) : B.card < C.card := by
  classical
  by_contra! fit
  let e : C ↪ B := (Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe] using fit)).some
  let f (v : V) := if h : v ∈ C then (e ⟨v,h⟩).val else Classical.choice ‹Nonempty W›
  have onC {v} (h : v ∈ C) : f v = (e ⟨v,h⟩).val := by simp [f,h]
  apply free (extend_leaves G X C f ?_ ?_ ?_)
  · intro a ha b hb eq
    rw [onC ha,onC hb] at eq
    exact congrArg Subtype.val (e.injective (Subtype.ext eq))
  · intro a ha b hb adj
    exact (ind a ha b hb adj).elim
  · intro v hv
    obtain ⟨c,hc,_,uniq⟩ := leaf v hv
    exact ⟨c,hc,uniq,by rw [onC hc]; exact ample _ (e ⟨c,hc⟩).property⟩

theorem count_after_hubs {W : Type*} [Fintype W] (X Y : SimpleGraph W)
    (B : Finset W) (d q Q : ℕ)
    (outside : ∀ u ∉ B, Y.neighborFinset u = X.neighborFinset u \ B)
    (cap : ∀ u, Y.degree u ≤ q)
    (few : (univ.filter fun u => d < Y.degree u).card ≤ Q) :
    2*X.edgeFinset.card ≤ (2*B.card+d)*Fintype.card W + q*Q := by
  classical
  let n := Fintype.card W
  have orig (v : W) : X.degree v ≤ Y.degree v + B.card + (if v ∈ B then n else 0) := by
    by_cases hv : v ∈ B
    · have deg : X.degree v ≤ n := by rw [← X.card_neighborFinset_eq_degree]; exact card_le_univ _
      simp [hv]; omega
    · have sub := card_le_card (inter_subset_right (s₁ := X.neighborFinset v) (s₂ := B))
      have sum := card_sdiff_add_card_inter (X.neighborFinset v) B
      rw [← outside v hv,Y.card_neighborFinset_eq_degree,X.card_neighborFinset_eq_degree] at sum
      simp [hv]; omega
  have rest (v : W) : Y.degree v ≤ d + (if d<Y.degree v then q else 0) := by
    have := cap v
    split_ifs <;> omega
  have sumX := sum_le_sum (s := univ) (fun v _ => orig v)
  have sumY := sum_le_sum (s := univ) (fun v _ => rest v)
  have allB : univ.filter (fun v => v ∈ B) = B := by ext; simp
  simp only [sum_add_distrib,←sum_filter,allB,sum_const,card_univ,nsmul_eq_mul,
    X.sum_degrees_eq_twice_card_edges] at sumX sumY
  have exc := Nat.mul_le_mul_right q few
  dsimp [n] at sumX
  nlinarith only [sumX,sumY,exc]

set_option maxHeartbeats 650000 in
theorem upper_bound {q n : ℕ} (G : SimpleGraph (Fin q)) (C : Finset (Fin q))
    (ind : ∀ a ∈ C, ∀ b ∈ C, ¬G.Adj a b)
    (leaf : ∀ v ∉ C, ∃ c ∈ C, G.Adj v c ∧ ∀ w, G.Adj v w → w=c)
    (X : SimpleGraph (Fin n)) (free : G.Free X) (qpos : 0<q) (largeN : q*((q+1)*(q+1))+q ≤ n) :
    ∃ h ≤ q, ∃ d ≤ q, h < (C.filter fun c => d < G.degree c).card ∧
      2*X.edgeFinset.card ≤ (2*h+d)*n + q*(q*((q+1)*(q+1))) := by
  classical
  let Q := q*((q+1)*(q+1))
  have Qpos : 0<Q := by dsimp [Q]; positivity
  have enough : Q+q ≤ n := largeN
  have : NeZero n := ⟨by omega⟩
  let B := univ.filter fun b => q ≤ X.degree b
  let Y : SimpleGraph (Fin n) := { Adj := fun a b => X.Adj a b ∧ a ∉ B ∧ b ∉ B
                                   symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
                                   loopless := ⟨fun v h => h.1.ne rfl⟩ }
  let _ : DecidableRel Y.Adj := fun a b => Classical.propDecidable _
  have sub : Y ≤ X := fun _ _ h => h.1
  have iso : ∀ b ∈ B, ∀ w, ¬Y.Adj b w := fun _ hb _ h => h.2.1 hb
  have ample (b) (hb : b ∈ B) : Fintype.card (Fin q)-1 ≤ X.degree b := by
    have := (mem_filter.mp hb).2
    rw [Fintype.card_fin]; omega
  have hcap := hub_cap G X C B ind leaf ample free
  have cs : C.card ≤ q := by simpa using card_le_univ C
  have outside (u) (hu : u ∉ B) : Y.neighborFinset u = X.neighborFinset u \ B := by
    ext v
    simp only [mem_sdiff,SimpleGraph.mem_neighborFinset]
    change (X.Adj u v ∧ u ∉ B ∧ v ∉ B) ↔ _
    simp [hu]
  have empty (u) (hu : u ∈ B) : Y.degree u=0 := by
    rw [← Y.card_neighborFinset_eq_degree,card_eq_zero]
    ext v
    simp [SimpleGraph.mem_neighborFinset,iso u hu v]
  have bound (u) : Y.degree u ≤ q := by
    by_cases hu : u ∈ B
    · simp [empty u hu]
    · have lim : X.degree u < q := lt_of_not_ge (fun h => hu (mem_filter.mpr ⟨mem_univ _,h⟩))
      rw [← Y.card_neighborFinset_eq_degree,outside u hu]
      exact (card_le_card sdiff_subset).trans (by simpa using lim.le)
  let F (d : ℕ) := univ.filter fun w => w ∉ B ∧ d ≤ Y.degree w
  let candidates := (range (q+1)).filter fun d => Q ≤ (F d).card
  have base : 0 ∈ candidates := by
    have f0 : F 0 = Bᶜ := by ext; simp [F]
    have b := card_compl_add_card B
    rw [Fintype.card_fin] at b
    exact mem_filter.mpr ⟨by simp,by rw [f0]; omega⟩
  let d := candidates.max' ⟨0,base⟩
  have hd : d ∈ candidates := candidates.max'_mem _
  obtain ⟨rangeD,numerous⟩ := mem_filter.mp hd
  have dq : d ≤ q := by have := mem_range.mp rangeD; omega
  have many : B.card < (C.filter fun c => d < G.degree c).card := by
    by_contra! small
    exact free (many_centers_embed G X Y C B d q ind leaf sub iso ample bound small (by
      simp only [Fintype.card_fin]
      unfold F at numerous
      convert numerous using 2; congr!))
  have few : (univ.filter fun u => d < Y.degree u).card ≤ Q := by
    have eq : (univ.filter fun u => d<Y.degree u) = F (d+1) := by
      ext u
      simp only [F,mem_filter,mem_univ,true_and]
      constructor
      · intro gt
        exact ⟨fun h => by rw [empty u h] at gt; omega,gt⟩
      · exact fun h => h.2
    rw [eq]
    by_cases last : d=q
    · have e : F (d+1)=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro u hu
        have := (mem_filter.mp hu).2.2
        have := bound u
        omega
      simp [e]
    · by_contra! many
      have mem : d+1 ∈ candidates := mem_filter.mpr ⟨mem_range.mpr (by omega),many.le⟩
      have bad : d+1 ≤ d := le_max' _ _ mem
      omega
  refine ⟨B.card,by omega,d,dq,many,?_⟩
  simpa only [Fintype.card_fin] using count_after_hubs X Y B d q Q (by
    intro u hu; convert outside u hu using 2; congr!) bound (by convert few using 2)



theorem centers {q : ℕ} (G : SimpleGraph (Fin q)) (active : ∀ v, ¬G.IsIsolated v)
    (star : ∀ v w, G.Adj v w → G.degree v ≤ 1 ∨ G.degree w ≤ 1) :
    ∃ C : Finset (Fin q),
      (∀ a ∈ C, ∀ b ∈ C, ¬ G.Adj a b) ∧
      (∀ v ∉ C, ∃ c ∈ C, G.Adj v c ∧ ∀ w, G.Adj v w → w=c) := by
  classical
  let C := univ.filter fun v => 1<G.degree v ∨ ∃ w, G.Adj v w ∧ G.degree w ≤ 1 ∧ v<w
  have member {v} : v ∈ C ↔ 1<G.degree v ∨ ∃ w, G.Adj v w ∧ G.degree w ≤ 1 ∧ v<w := by simp [C]
  have unique {v u w} (low : G.degree v ≤ 1) (a : G.Adj v u) (b : G.Adj v w) : u=w :=
    card_le_one.mp ((G.card_neighborFinset_eq_degree v).symm ▸ low) _ ((G.mem_neighborFinset _ _).mpr a) _ ((G.mem_neighborFinset _ _).mpr b)
  have along {v w} (adj : G.Adj v w) (low : G.degree v ≤ 1) :
      v ∈ C ↔ G.degree w ≤ 1 ∧ v<w := by
    rw [member]
    constructor
    · rintro (high | ⟨u,edge,deg,lt⟩)
      · omega
      · exact unique low edge adj ▸ And.intro deg lt
    · exact fun ⟨deg,lt⟩ => Or.inr ⟨w,adj,deg,lt⟩
  refine ⟨C,?_,?_⟩
  · intro a ha b hb ab
    rcases star a b ab with low | low
    · obtain ⟨lowB,lt⟩ := (along ab low).mp ha
      exact lt_asymm lt ((along ab.symm lowB).mp hb).2
    · obtain ⟨lowA,lt⟩ := (along ab.symm low).mp hb
      exact lt_asymm lt ((along ab lowA).mp ha).2
  · intro v hv
    obtain ⟨w,adj⟩ := exists_adj_iff_not_isIsolated.mpr (active v)
    have low : G.degree v ≤ 1 := le_of_not_gt (fun hi => hv (member.mpr (Or.inl hi)))
    refine ⟨w,?_,adj,fun _ edge => unique low edge adj⟩
    by_cases high : 1<G.degree w
    · exact member.mpr (Or.inl high)
    · apply (along adj.symm (le_of_not_gt high)).mpr
      exact ⟨low,lt_of_le_of_ne (le_of_not_gt (fun lt => hv ((along adj low).mpr ⟨le_of_not_gt high,lt⟩))) adj.ne.symm⟩

theorem free_of_hubs {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (X : SimpleGraph W)
    (C : Finset V) (B : Finset W) (d : ℕ)
    (separate : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → Disjoint (insert u (G.neighborFinset u)) (insert v (G.neighborFinset v)))
    (low : ∀ x ∉ B, ((X.neighborFinset x) \ B).card ≤ d)
    (many : B.card < (C.filter fun u => d < G.degree u).card) : G.Free X := by
  classical
  rintro ⟨e⟩
  let S := C.filter fun u => d < G.degree u
  have touch (u : S) : ∃ v ∈ insert u.val (G.neighborFinset u.val), e v ∈ B := by
    by_contra! empty
    have out := empty u.val (mem_insert_self ..)
    have sub : (G.neighborFinset u.val).image (fun v => e v) ⊆ (X.neighborFinset (e u.val)) \ B := by
      intro z hz
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
      exact mem_sdiff.mpr ⟨(X.mem_neighborFinset _ _).mpr (e.toHom.map_rel' ((G.mem_neighborFinset _ _).mp hv)),
        empty v (mem_insert_of_mem hv)⟩
    have count := (card_le_card sub).trans (low _ out)
    rw [card_image_of_injective _ (show Function.Injective (fun v => e v) from e.injective),G.card_neighborFinset_eq_degree] at count
    exact (not_lt_of_ge count) (mem_filter.mp u.property).2
  choose v near inB using touch
  let f (u : S) : B := ⟨e (v u),inB u⟩
  have inj : Function.Injective f := by
    intro u w eq
    by_contra ne
    have h := e.injective (congrArg Subtype.val eq : e (v u)=e (v w))
    have dis := separate _ (mem_filter.mp u.property).1 _ (mem_filter.mp w.property).1 (fun he => ne (Subtype.ext he))
    exact disjoint_left.mp dis (near u) (h.symm ▸ near w)
  have sz := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_coe] at sz
  exact many.not_ge sz

theorem disjoint_stars {V : Type*} [Fintype V] (G : SimpleGraph V) (C : Finset V)
    (ind : ∀ a ∈ C, ∀ b ∈ C, ¬G.Adj a b)
    (leaf : ∀ v ∉ C, ∃ c ∈ C, G.Adj v c ∧ ∀ w, G.Adj v w → w=c)
    {a b} (ha : a ∈ C) (hb : b ∈ C) (ne : a ≠ b) :
    Disjoint (insert a (G.neighborFinset a)) (insert b (G.neighborFinset b)) := by
  classical
  refine disjoint_left.mpr ?_
  intro v va vb
  rcases mem_insert.mp va with eq | edge <;> rcases mem_insert.mp vb with eq' | edge'
  · exact ne (eq.symm.trans eq')
  · exact ind b hb a ha (eq ▸ (G.mem_neighborFinset _ _).mp edge')
  · exact ind a ha b hb (eq' ▸ (G.mem_neighborFinset _ _).mp edge)
  · have av := (G.mem_neighborFinset _ _).mp edge
    have bv := (G.mem_neighborFinset _ _).mp edge'
    obtain ⟨_,_,_,unique⟩ := leaf v (fun hv => ind a ha v hv av)
    exact ne ((unique _ av.symm).trans (unique _ bv.symm).symm)


theorem block_construction {V : Type*} [Fintype V] (G : SimpleGraph V) (C : Finset V)
    (ind : ∀ a ∈ C, ∀ b ∈ C, ¬G.Adj a b)
    (leaf : ∀ v ∉ C, ∃ c ∈ C, G.Adj v c ∧ ∀ w, G.Adj v w → w=c)
    (h d l : ℕ) (many : h < (C.filter fun c => d < G.degree c).card) :
    ∃ X : SimpleGraph ((Fin h) ⊕ (Fin l × Fin (d+1))), G.Free X ∧
      2*X.edgeFinset.card = (2*h+d)*(l*(d+1)) := by
  classical
  let W := (Fin h) ⊕ (Fin l × Fin (d+1))
  let rel (u v : W) : Prop := match u,v with
    | .inl _,.inl _ => False
    | .inl _,.inr _ | .inr _,.inl _ => True
    | .inr x,.inr y => x.1=y.1 ∧ x.2 ≠ y.2
  let X : SimpleGraph W := { Adj := rel, symm := ⟨by
                              rintro (a|a) (b|b) ab <;> simp_all [rel,eq_comm]⟩
                             loopless := ⟨by rintro (a|a) <;> simp [rel]⟩ }
  let B : Finset W := univ.map Function.Embedding.inl
  let R : Finset W := univ.map Function.Embedding.inr
  have szB : B.card=h := by simp [B]
  have szR : R.card=l*(d+1) := by simp [R]
  have inB (i : Fin h) : Sum.inl i ∈ B := mem_map.mpr ⟨_,mem_univ _,rfl⟩
  have notB (p : Fin l × Fin (d+1)) : Sum.inr p ∉ B := by
    intro hp
    obtain ⟨_,_,eq⟩ := mem_map.mp hp
    cases eq
  have left (i : Fin h) : X.neighborFinset (.inl i) = R := by
    ext v
    rw [X.mem_neighborFinset]
    cases v with
    | inl j =>
      constructor
      · exact False.elim
      · intro hj
        obtain ⟨_,_,eq⟩ := mem_map.mp hj
        cases eq
    | inr p => exact iff_of_true trivial (mem_map.mpr ⟨p,mem_univ _,rfl⟩)
  have right (b : Fin l) (j : Fin (d+1)) :
      X.neighborFinset (.inr (b,j)) = B ∪ ((univ.erase j).image (fun k => Sum.inr (b,k))) := by
    ext v
    rw [X.mem_neighborFinset,mem_union]
    cases v with
    | inl i => exact iff_of_true trivial (Or.inl (inB i))
    | inr p =>
      obtain ⟨a,k⟩ := p
      rw [or_iff_right (notB _)]
      change (b=a ∧ j ≠ k) ↔ _
      constructor
      · rintro ⟨rfl,ne⟩
        exact mem_image.mpr ⟨k,mem_erase.mpr ⟨ne.symm,mem_univ _⟩,rfl⟩
      · intro h
        obtain ⟨z,hz,eq⟩ := mem_image.mp h
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Sum.inr.inj eq)
        exact ⟨rfl,(mem_erase.mp hz).1.symm⟩
  have separate (b : Fin l) (j : Fin (d+1)) : Disjoint B ((univ.erase j).image (fun k => Sum.inr (b,k))) := by
    apply Finset.disjoint_left.mpr
    intro w hw he
    obtain ⟨z,_,rfl⟩ := mem_image.mp he
    exact notB _ hw
  have dr (b : Fin l) (j : Fin (d+1)) : X.degree (.inr (b,j))=h+d := by
    rw [← X.card_neighborFinset_eq_degree,right,card_union_of_disjoint (separate ..),szB,
      card_image_of_injective _ (show Function.Injective (fun k : Fin (d+1) => (Sum.inr (b,k) : W)) by intro x y eq; simpa using eq)]
    simp
  have dl (i : Fin h) : X.degree (.inl i)=l*(d+1) := by rw [← X.card_neighborFinset_eq_degree,left,szR]
  refine ⟨X,free_of_hubs G X C B d (fun _ ha _ hb ne => disjoint_stars G C ind leaf ha hb ne) ?_ (by simpa [szB] using many),?_⟩
  · rintro (a|⟨b,j⟩) out
    · exact (out (mem_map.mpr ⟨a,mem_univ _,rfl⟩)).elim
    · have sub : B ⊆ X.neighborFinset (.inr (b,j)) := by rw [right]; exact subset_union_left
      have eq := card_sdiff_of_subset sub
      rw [X.card_neighborFinset_eq_degree,dr,szB] at eq
      convert (show h+d-h ≤ d by omega) using 1
      exact Eq.trans (by congr! 4) eq
  · rw [← X.sum_degrees_eq_twice_card_edges,Fintype.sum_sum_type]
    simp only [dl,dr,Fintype.card_prod,sum_const,card_univ,Fintype.card_fin,smul_eq_mul]
    ring

theorem padding {V W : Type*} [Fintype W] (G : SimpleGraph V) (active : ∀ v, ¬G.IsIsolated v)
    (X : SimpleGraph W) (free : G.Free X) (m : ℕ) (fit : Fintype.card W ≤ m) :
    X.edgeFinset.card ≤ extremalNumber m G := by
  classical
  let k := m-Fintype.card W
  let Z := X ⊕g (⊥ : SimpleGraph (Fin k))
  have hf : G.Free Z := by
    rintro ⟨e⟩
    have original (v : V) : ∃ w : W, e v = Sum.inl w := by
      cases h : e v with
      | inl w => exact ⟨w,rfl⟩
      | inr i =>
        obtain ⟨u,adj⟩ := exists_adj_iff_not_isIsolated.mpr (active v)
        have a := e.toHom.map_rel' adj
        change Z.Adj (e v) (e u) at a
        rw [h] at a
        cases hu : e u with
        | inl t => rw [hu] at a; exact (not_adj_sum_inl_inr t i a.symm).elim
        | inr j => rw [hu] at a; exact (sum_adj_inr.mp a).elim
    choose f he using original
    apply free
    refine ⟨⟨⟨f,?_⟩,?_⟩⟩
    · intro a b adj
      have h := e.toHom.map_rel' adj
      change Z.Adj (e a) (e b) at h
      rw [he a,he b] at h
      exact sum_adj_inl.mp h
    · intro a b eq
      exact e.injective ((he a).trans ((congrArg Sum.inl eq).trans (he b).symm))
  have sumedges : Z.edgeFinset.card=X.edgeFinset.card := by
    simp only [Z,edgeFinset_card]
    have eq := Fintype.card_congr (edgeSetSumEquiv (G:=X) (H:=(⊥ : SimpleGraph (Fin k))))
    simpa using eq
  have hh := card_edgeFinset_le_extremalNumber hf
  have sz : Fintype.card (W ⊕ Fin k)=m := by simp [k,fit]
  simpa only [sumedges,sz] using hh

theorem lower_bound {V : Type*} [Fintype V] (G : SimpleGraph V) (C : Finset V)
    (ind : ∀ a ∈ C, ∀ b ∈ C, ¬G.Adj a b)
    (leaf : ∀ v ∉ C, ∃ c ∈ C, G.Adj v c ∧ ∀ w, G.Adj v w → w=c)
    (active : ∀ v, ¬G.IsIsolated v) (h d m : ℕ) (fit : h ≤ m)
    (many : h < (C.filter fun c => d < G.degree c).card) :
    (2*h+d)*m ≤ 2*extremalNumber m G + (2*h+d)*(h+d) := by
  classical
  let l := (m-h)/(d+1)
  obtain ⟨X,free,edges⟩ := block_construction G C ind leaf h d l many
  have rle : l*(d+1) ≤ m-h := Nat.div_mul_le_self ..
  have sz : Fintype.card (Fin h ⊕ (Fin l × Fin (d+1))) ≤ m := by
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega
  have cap := padding G active X free m sz
  have rem : (m-h)%(d+1) < d+1 := Nat.mod_lt _ (by omega)
  have total := Nat.mod_add_div (m-h) (d+1)
  have len : m ≤ l*(d+1)+(h+d) := by dsimp [l]; rw [Nat.mul_comm (d+1)] at total; omega
  have limit := Nat.mul_le_mul_left (2*h+d) len
  rw [Nat.mul_add,← edges] at limit
  omega


theorem slope {q : ℕ} (G : SimpleGraph (Fin q)) (active : ∀ v, ¬G.IsIsolated v)
    (star : ∀ v w, G.Adj v w → G.degree v ≤ 1 ∨ G.degree w ≤ 1) (notBot : G ≠ ⊥) (qpos : 0<q) :
    ∃ s N E : ℕ, ∀ n ≥ N, 2*extremalNumber n G ≤ s*n + E ∧ s*n ≤ 2*extremalNumber n G + E := by
  classical
  obtain ⟨C,ind,leaf⟩ := centers G active star
  let Q := q*((q+1)*(q+1))
  let N := Q+q
  have each (n) (hn : N ≤ n) : ∃ h ≤ q, ∃ d ≤ q, h < (C.filter fun c => d<G.degree c).card ∧
      2*extremalNumber n G ≤ (2*h+d)*n + q*Q := by
    obtain ⟨X,dx,ext⟩ := exists_isExtremal_free (V := Fin n) notBot
    let _ : DecidableRel X.Adj := dx
    have eq : X.edgeFinset.card=extremalNumber n G := by simpa using card_edgeFinset_of_isExtremal_free ext
    obtain ⟨h,hq,d,dq,many,upper⟩ := upper_bound G C ind leaf X ext.prop qpos hn
    refine ⟨h,hq,d,dq,many,?_⟩
    rw [←eq]
    convert upper using 2; congr!
  let A := ((range (q+1)).product (range (q+1))).filter fun p => p.1 < (C.filter fun c => p.2 < G.degree c).card
  have mem {h d} : (h,d) ∈ A ↔ h ≤ q ∧ d ≤ q ∧ h < (C.filter fun c => d<G.degree c).card := by
    simp [A,and_assoc]
  obtain ⟨h0,hh,d0,dd,big,_⟩ := each N le_rfl
  obtain ⟨⟨h,d⟩,inside,maxi⟩ := exists_max_image A (fun p => 2*p.1+p.2) ⟨_,mem.mpr ⟨hh,dd,big⟩⟩
  obtain ⟨hq,dq,many⟩ := mem.mp inside
  let s := 2*h+d
  refine ⟨s,N,q*Q+s*(h+d),?_⟩
  intro n hn
  obtain ⟨u,uq,v,vq,adm,ub⟩ := each n hn
  have cap : 2*u+v ≤ s := maxi (u,v) (mem.mpr ⟨uq,vq,adm⟩)
  have hi := Nat.mul_le_mul_right n cap
  have large : h ≤ n := by dsimp [N] at hn; omega
  have low := lower_bound G C ind leaf active h d n large many
  change s*n ≤ 2*extremalNumber n G+s*(h+d) at low
  constructor <;> omega

theorem rational_threshold (f : ℕ → ℕ) (s N E : ℕ)
    (bounds : ∀ n ≥ N, 2*f n ≤ s*n+E ∧ s*n ≤ 2*f n+E)
    (a b : ℚ) (lt : a<b) (freq : ∀ k, ∃ n ≥ k, b*n < (f n : ℚ)) :
    ∃ M, ∀ m ≥ M, a*m ≤ (f m : ℚ) := by
  have delta : 0<b-a := sub_pos.mpr lt
  obtain ⟨t,ht⟩ := exists_nat_gt ((E:ℚ)/(b-a))
  have absorb (n : ℕ) (hn : t ≤ n) : (E:ℚ) < (b-a)*n := by
    have lim := ht.trans_le (show (t:ℚ) ≤ n by exact_mod_cast hn)
    exact (mul_comm (n:ℚ) (b-a)) ▸ (div_lt_iff₀ delta).mp lim
  obtain ⟨n,hn,hit⟩ := freq (max 1 (max t N))
  have start : N ≤ n := by omega
  have big : t ≤ n := by omega
  have upper : 2*(f n:ℚ) ≤ (s:ℚ)*n+E := by exact_mod_cast (bounds n start).1
  have slope : a+b < (s:ℚ) := by
    apply (mul_lt_mul_iff_left₀ (show (0:ℚ)<n by exact_mod_cast (show 0<n by omega))).mp
    nlinarith [absorb n big]
  refine ⟨max t N,?_⟩
  intro m hm
  have sm := mul_le_mul_of_nonneg_right slope.le (show (0:ℚ) ≤ m by positivity)
  have low : (s:ℚ)*m ≤ 2*(f m:ℚ)+E := by exact_mod_cast (bounds m (by omega)).2
  nlinarith [absorb m (by omega)]

end E713Stars

theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_i_R1_H2_R1.H2 := by
  intro q G _ _ edges active _ _ branching star a b lt freq
  classical
  have nontrivial : G ≠ ⊥ := by
    intro eq
    rw [edgeFinset_eq_empty.mpr eq] at edges
    simp at edges
  have qpos : 0<q := by obtain ⟨v,_⟩ := branching; exact (Nat.zero_le v.val).trans_lt v.isLt
  obtain ⟨s,N,E,bounds⟩ := E713Stars.slope G active star nontrivial qpos
  exact E713Stars.rational_threshold (fun n => extremalNumber n G) s N E bounds a b lt freq
