import OMAReductions.R_Erdos617_erdos_617_variants_r_eq_4_R1

/-! # The nine-vertex Ramsey step for Erdős 617 -/
namespace OMA.FourColorLocal
open Finset SimpleGraph
open scoped Classical
variable {V : Type} [DecidableEq V]

private def Triangle (G : SimpleGraph V) (T : Finset V) : Prop :=
  T.card = 3 ∧ ∀ a ∈ T, ∀ b ∈ T, a ≠ b → G.Adj a b

private lemma ramseySix (G : SimpleGraph V) (X : Finset V) (six : 6 ≤ X.card)
    (edges : ∀ a ∈ X, ∀ b ∈ X, ∀ d ∈ X, a ≠ b → a ≠ d → b ≠ d →
      G.Adj a b ∨ G.Adj a d ∨ G.Adj b d) :
    ∃ T ⊆ X, Triangle G T := by
  classical
  have mk (a b d : V) (ha : a ∈ X) (hb : b ∈ X) (hd : d ∈ X)
      (ab : G.Adj a b) (ad : G.Adj a d) (bd : G.Adj b d) : ∃ T ⊆ X, Triangle G T := by
    refine ⟨{a,b,d},(by
      intro z hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl|rfl|rfl <;> assumption),by simp [ab.ne,ad.ne,bd.ne],?_⟩
    intro i hi j hj ne
    simp only [mem_insert,mem_singleton] at hi hj
    rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl <;>
      first | assumption | exact False.elim (ne rfl) | apply SimpleGraph.Adj.symm; assumption
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0 < X.card)
  let A := (X.erase x).filter (G.Adj x)
  let B := (X.erase x).filter (fun a => ¬ G.Adj x a)
  have sum : A.card + B.card = X.card - 1 := by
    simpa [A,B,card_erase_of_mem hx] using card_filter_add_card_filter_not (s := X.erase x) (p := G.Adj x)
  by_cases big : 2 < A.card
  · obtain ⟨a,b,d,ha,hb,hd,ab,ad,bd⟩ := two_lt_card_iff.mp big
    have extA (y) (hy : y ∈ A) : y ∈ X ∧ G.Adj x y :=
      ⟨(mem_erase.mp (mem_filter.mp hy).1).2,(mem_filter.mp hy).2⟩
    rcases edges a (extA a ha).1 b (extA b hb).1 d (extA d hd).1 ab ad bd with e|e|e
    · exact mk x a b hx (extA a ha).1 (extA b hb).1 (extA a ha).2 (extA b hb).2 e
    · exact mk x a d hx (extA a ha).1 (extA d hd).1 (extA a ha).2 (extA d hd).2 e
    · exact mk x b d hx (extA b hb).1 (extA d hd).1 (extA b hb).2 (extA d hd).2 e
  · obtain ⟨a,b,d,ha,hb,hd,ab,ad,bd⟩ := two_lt_card_iff.mp (by omega : 2 < B.card)
    have info (y) (hy : y ∈ B) : y ≠ x ∧ y ∈ X ∧ ¬ G.Adj x y :=
      ⟨(mem_erase.mp (mem_filter.mp hy).1).1,(mem_erase.mp (mem_filter.mp hy).1).2,(mem_filter.mp hy).2⟩
    have link (y z) (hy : y ∈ B) (hz : z ∈ B) (ne : y ≠ z) : G.Adj y z :=
      ((edges x hx y (info y hy).2.1 z (info z hz).2.1 (info y hy).1.symm (info z hz).1.symm ne
        ).resolve_left (info y hy).2.2).resolve_left (info z hz).2.2
    exact mk a b d (info a ha).2.1 (info b hb).2.1 (info d hd).2.1
      (link a b ha hb ab) (link a d ha hd ad) (link b d hb hd bd)
private lemma ramseyNine [Fintype V] (G : SimpleGraph V) (X : Finset V) (size : 9 ≤ X.card)
    (edges : ∀ a ∈ X, ∀ b ∈ X, ∀ d ∈ X, a ≠ b → a ≠ d → b ≠ d →
      G.Adj a b ∨ G.Adj a d ∨ G.Adj b d) :
    ∃ Q ⊆ X, Q.card = 4 ∧ G.IsClique (Q : Set V) := by
  classical
  obtain ⟨Y,ysub,ycard⟩ := exists_subset_card_eq size
  by_contra! no
  have cap (Q : Finset V) (sub : Q ⊆ X) (cl : G.IsClique (Q : Set V)) : Q.card ≤ 3 := by
    by_contra! big
    obtain ⟨T,tsub,tc⟩ := exists_subset_card_eq big
    exact no T (tsub.trans sub) tc (fun a ha b hb ne => cl (tsub ha) (tsub hb) ne)
  let H := G.induce (Y : Set V)
  have deg (v : Y) : H.degree v = 5 := by
    let A := (Y.erase v.val).filter (G.Adj v.val)
    let B := (Y.erase v.val).filter (fun b => ¬ G.Adj v.val b)
    have eq : A.card + B.card = 8 := by
      simpa [A,B,card_erase_of_mem v.property,ycard] using
        card_filter_add_card_filter_not (s := Y.erase v.val) (p := G.Adj v.val)
    have inA (a : V) (ha : a ∈ A) : a ∈ Y ∧ G.Adj v.val a :=
      ⟨mem_of_mem_erase (mem_filter.mp ha).1,(mem_filter.mp ha).2⟩
    have inB (b : V) (hb : b ∈ B) : b ∈ Y ∧ b ≠ v.val ∧ ¬ G.Adj v.val b :=
      ⟨mem_of_mem_erase (mem_filter.mp hb).1,ne_of_mem_erase (mem_filter.mp hb).1,(mem_filter.mp hb).2⟩
    have smallB := cap B (fun b hb => ysub (inB b hb).1) (by
      intro b hb d hd ne
      rcases edges _ (ysub v.property) _ (ysub (inB b hb).1) _ (ysub (inB d hd).1)
          (inB b hb).2.1.symm (inB d hd).2.1.symm ne with e|e|e
      · exact ((inB b hb).2.2 e).elim
      · exact ((inB d hd).2.2 e).elim
      · exact e)
    have smallA : A.card ≤ 5 := by
      by_contra! big
      obtain ⟨T,tsub,tri⟩ := ramseySix G A big (fun a ha b hb d hd =>
        edges a (ysub (inA a ha).1) b (ysub (inA b hb).1) d (ysub (inA d hd).1))
      have vt : v.val ∉ T := fun h => (inA _ (tsub h)).2.ne rfl
      have cover : insert v.val T ⊆ X := insert_subset (ysub v.property)
        (fun a ha => ysub (inA a (tsub ha)).1)
      have clique : G.IsClique ((insert v.val T : Finset V) : Set V) := by
        intro a ha b hb ne
        rcases mem_insert.mp ha with rfl|ha <;> rcases mem_insert.mp hb with rfl|hb
        · exact (ne rfl).elim
        · exact (inA _ (tsub hb)).2
        · exact (inA _ (tsub ha)).2.symm
        · exact tri.2 a ha b hb ne
      have bad := cap _ cover clique
      rw [card_insert_of_notMem vt,tri.1] at bad
      omega
    have count : H.degree v = A.card := by
      change (H.neighborFinset v).card = A.card
      apply card_bij (fun (b : Y) _ => b.val)
      · intro b hb
        have adj : G.Adj v.val b.val := (H.mem_neighborFinset v b).mp hb
        exact mem_filter.mpr ⟨mem_erase.mpr ⟨adj.ne',b.property⟩,adj⟩
      · intro a _ b _ eq
        exact Subtype.ext eq
      · intro b hb
        obtain ⟨hy,adj⟩ := inA b hb
        exact ⟨⟨b,hy⟩,(H.mem_neighborFinset v ⟨b,hy⟩).mpr adj,rfl⟩
    omega
  have odd := H.sum_degrees_eq_twice_card_edges
  simp_rw [deg] at odd
  simp [ycard] at odd
  omega


private lemma clique_count [Fintype V] (G : SimpleGraph V) (T : Finset V)
    (cl : G.IsClique (T : Set V)) : (G.induce (T : Set V)).edgeFinset.card = T.card.choose 2 := by
  classical
  have eq := SimpleGraph.induce_eq_top.mpr cl
  have ce := congrArg (fun H : SimpleGraph T => Nat.card H.edgeSet) eq
  simp only [Nat.card_eq_fintype_card,card_edgeSet] at ce
  exact ce.trans (by simpa only [Fintype.card_coe] using (card_edgeFinset_top_eq_card_choose_two (V := T)))

private lemma extendClique [Fintype V] (G : SimpleGraph V) {T : Finset V}
    (four : T.card = 4) (cl : G.IsClique (T : Set V)) {z : V} (zt : z ∉ T)
    {a b : V} (ha : a ∈ T) (hb : b ∈ T) (ab : a ≠ b) (za : G.Adj z a) (zb : G.Adj z b) :
    8 ≤ (G.induce ((insert z T : Finset V) : Set V)).edgeFinset.card := by
  classical
  let E (S : Finset V) := G.edgeFinset ∩ S.sym2
  have count (S : Finset V) : (E S).card = (G.induce (S : Set V)).edgeFinset.card := by
    rw [← G.card_filter_edgeFinset_toFinset_subset, G.filter_edgeFinset_toFinset_subset]
  have orig : (E T).card = 6 := by
    rw [count,clique_count G T cl,four]
    decide
  have old (w : V) : s(z,w) ∉ E T := fun e => zt (mk_mem_sym2_iff.mp (mem_inter.mp e).2).1
  have new (w : V) (hw : w ∈ T) (adj : G.Adj z w) : s(z,w) ∈ E (insert z T) :=
    mem_inter.mpr ⟨mem_edgeFinset.mpr adj,mk_mem_sym2_iff.mpr ⟨mem_insert_self ..,mem_insert_of_mem hw⟩⟩
  have ne : s(z,a) ≠ s(z,b) := fun e => ab (Sym2.congr_right.mp e)
  have sub : insert s(z,a) (insert s(z,b) (E T)) ⊆ E (insert z T) := by
    refine insert_subset (new a ha za) (insert_subset (new b hb zb) ?_)
    intro e he
    obtain ⟨eg,et⟩ := mem_inter.mp he
    exact mem_inter.mpr ⟨eg,mem_sym2_iff.mpr (fun w hw => mem_insert_of_mem (mem_sym2_iff.mp et w hw))⟩
  have le := card_le_card sub
  simpa [ne,old,orig,count (insert z T)] using le

private lemma localRamsey [Fintype V] (G : SimpleGraph V) (X : Finset V) (size : 9 ≤ X.card)
    (edges : ∀ a ∈ X, ∀ b ∈ X, ∀ d ∈ X, a ≠ b → a ≠ d → b ≠ d →
      G.Adj a b ∨ G.Adj a d ∨ G.Adj b d) :
    ∃ S ⊆ X, S.card = 5 ∧ 8 ≤ (G.induce (S : Set V)).edgeFinset.card := by
  classical
  obtain ⟨Q,qsub,four,cl⟩ := ramseyNine G X size edges
  by_contra! sparse
  let Z := X \ Q
  have small (a) (ha : a ∈ Z) : (Q.filter (G.Adj a)).card ≤ 1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra ne
    obtain ⟨au,eu⟩ := mem_filter.mp hu
    obtain ⟨av,ev⟩ := mem_filter.mp hv
    obtain ⟨ax,aq⟩ := mem_sdiff.mp ha
    have large := extendClique G four cl aq au av ne eu ev
    have bound := sparse (insert a Q) (insert_subset ax qsub) (by simp [four,aq])
    omega
  have complete : G.IsClique (Z : Set V) := by
    intro a ha b hb ne
    let seen := Q.filter (G.Adj a) ∪ Q.filter (G.Adj b)
    have s1 := small a ha
    have s2 := small b hb
    have sum := card_union_le (Q.filter (G.Adj a)) (Q.filter (G.Adj b))
    have lt : seen.card < Q.card := by dsimp [seen]; omega
    obtain ⟨d,hd,out⟩ := exists_mem_notMem_of_card_lt_card lt
    have na : ¬G.Adj a d := fun h => out (mem_union_left _ (mem_filter.mpr ⟨hd,h⟩))
    have nb : ¬G.Adj b d := fun h => out (mem_union_right _ (mem_filter.mpr ⟨hd,h⟩))
    obtain ⟨ax,aq⟩ := mem_sdiff.mp ha
    obtain ⟨bx,bq⟩ := mem_sdiff.mp hb
    exact ((edges a ax b bx d (qsub hd) ne (fun e => aq (e ▸ hd)) (fun e => bq (e ▸ hd))
      ).resolve_right (not_or.mpr ⟨na,nb⟩))
  have five : 5 ≤ Z.card := by dsimp [Z]; rw [card_sdiff_of_subset qsub]; omega
  obtain ⟨T,tsub,tc⟩ := exists_subset_card_eq five
  have clique : G.IsClique (T : Set V) := fun _ ha _ hb ne => complete (tsub ha) (tsub hb) ne
  have count := clique_count G T clique
  rw [tc] at count
  have low := sparse T (tsub.trans sdiff_subset) tc
  norm_num [Nat.choose] at count
  omega

end OMA.FourColorLocal

theorem OMA.solution : OMA.R_Erdos617_erdos_617_variants_r_eq_4_R1.H1 := by
  intro V _ _ G X size h
  exact OMA.FourColorLocal.localRamsey G X size h
