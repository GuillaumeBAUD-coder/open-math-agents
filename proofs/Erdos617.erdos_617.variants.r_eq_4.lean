import FormalConjectures.ErdosProblems.«617»

/-! # Four colors on seventeen vertices (Erdős Problem 617, r = 4)
Combined from the reduction and step proofs:
- reductions/Erdos617.erdos_617.variants.r_eq_4.R1.lean
- proofs/Erdos617.erdos_617.variants.r_eq_4.R1.H1.lean
- proofs/Erdos617.erdos_617.variants.r_eq_4.R1.H2.lean
-/


/- # The nine-vertex Ramsey step for Erdős 617 -/
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


/- # The extremal edge count on seventeen vertices in Erdős 617
The graph decomposition follows Erdős and Gyárfás, “Split and balanced
colorings of complete graphs” (1999), Lemma 2. The counting argument below
treats both possible orders of the two vertex degrees uniformly.
Removing a minimum-degree vertex with its neighbors costs at least the square
of that degree less the number of edges among the neighbors.
-/
namespace OMA.SeventeenVertices
open Finset SimpleGraph
open scoped Classical
variable {V : Type} [DecidableEq V]

private noncomputable def ec (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (G.induce (S : Set V)).edgeFinset.card

private noncomputable def ns (G : SimpleGraph V) (S : Finset V) (a : V) : Finset V :=
  S.filter (G.Adj a)

private noncomputable def inc (G : SimpleGraph V) (A B : Finset V) : ℕ :=
  ∑ a ∈ A, (ns G B a).card

omit [DecidableEq V] in
private lemma mem_ns {G : SimpleGraph V} {S : Finset V} {a b : V} :
    b ∈ ns G S a ↔ b ∈ S ∧ G.Adj a b := by simp [ns]

omit [DecidableEq V] in
private lemma inc_sym (G : SimpleGraph V) (A B : Finset V) : inc G A B = inc G B A := by
  classical
  calc
    _ = ∑ a ∈ A, ∑ b ∈ B, (if G.Adj a b then 1 else 0 : ℕ) := by simp [inc,ns]
    _ = ∑ b ∈ B, ∑ a ∈ A, (if G.Adj a b then 1 else 0 : ℕ) := sum_comm
    _ = _ := by simp [inc,ns,G.adj_comm]

private lemma inc_union (G : SimpleGraph V) {A B : Finset V} (dis : Disjoint A B)
    (C : Finset V) : inc G (A ∪ B) C = inc G A C + inc G B C := sum_union dis

omit [DecidableEq V] in
private lemma degree_on (G : SimpleGraph V) (S : Finset V) (v : S) :
    (G.induce (S : Set V)).degree v = (ns G S v.val).card := by
  classical
  let H := G.induce (S : Set V)
  change (H.neighborFinset v).card = _
  apply card_bij (fun (b : S) _ => b.val)
  · intro b hb
    exact mem_ns.mpr ⟨b.property,(H.mem_neighborFinset v b).mp hb⟩
  · intro a _ b _ e
    exact Subtype.ext e
  · intro b hb
    obtain ⟨bs,adj⟩ := mem_ns.mp hb
    exact ⟨⟨b,bs⟩,(H.mem_neighborFinset v ⟨b,bs⟩).mpr adj,rfl⟩

omit [DecidableEq V] in
private lemma twice (G : SimpleGraph V) (S : Finset V) : inc G S S = 2 * ec G S := by
  classical
  have eq := (G.induce (S : Set V)).sum_degrees_eq_twice_card_edges
  simp_rw [degree_on G S] at eq
  calc
    inc G S S = ∑ v : S, (ns G S v.val).card := (S.sum_coe_sort (fun v => (ns G S v).card)).symm
    _ = _ := eq

-- Edges between the two parts contribute once to the degree sum from A.
private lemma partition (G : SimpleGraph V) {A B : Finset V} (dis : Disjoint A B) :
    ec G (A ∪ B) + ec G A = inc G A (A ∪ B) + ec G B := by
  have h := twice G (A ∪ B)
  rw [inc_union G dis,inc_sym G B (A ∪ B),inc_union G dis] at h
  have f := inc_sym G A (A ∪ B)
  rw [inc_union G dis,inc_sym G B A] at f
  have := twice G A
  have := twice G B
  omega

private lemma erase_isolated (G : SimpleGraph V) {S : Finset V} {v : V}
    (nov : v ∉ S) (isol : ∀ b ∈ S, ¬ G.Adj v b) : ec G (insert v S) = ec G S := by
  classical
  have part := partition G (A := {v}) (B := S) (by simpa using nov)
  have single : ec G {v} = 0 := by
    have hh := (G.induce (({v} : Finset V) : Set V)).card_edgeFinset_le_card_choose_two
    simpa [ec] using hh
  have empty : ns G (insert v S) v = ∅ := by
    ext b
    simp only [mem_ns,mem_insert,notMem_empty,iff_false,not_and]
    rintro (rfl|hb)
    · exact G.loopless.irrefl _
    · exact isol b hb
  simpa [Finset.singleton_union,inc,single,empty] using part

private lemma shell (G : SimpleGraph V) (U : Finset V) (x : V) (hx : x ∈ U) :
    let M := ns G U x
    let A := (U.erase x) \ M
    ec G U + ec G M = inc G M U + ec G A := by
  classical
  intro M A
  have xm : x ∉ M := fun h => (mem_ns.mp h).2.ne rfl
  have xa : x ∉ A := fun h => (ne_of_mem_erase (mem_sdiff.mp h).1) rfl
  have isol (a) (ha : a ∈ A) : ¬G.Adj x a := fun adj =>
    (mem_sdiff.mp ha).2 (mem_ns.mpr ⟨mem_of_mem_erase (mem_sdiff.mp ha).1,adj⟩)
  have dis : Disjoint M (insert x A) := by
    apply Finset.disjoint_left.mpr
    intro a am ia
    rcases mem_insert.mp ia with rfl|ha
    · exact xm am
    · exact (mem_sdiff.mp ha).2 am
  have cover : M ∪ insert x A = U := by
    ext a
    simp only [mem_union,mem_insert,mem_sdiff,mem_erase,A]
    constructor
    · rintro (am|rfl|⟨⟨_,au⟩,_⟩)
      · exact (mem_ns.mp am).1
      · exact hx
      · exact au
    · intro au
      by_cases am : a ∈ M
      · exact Or.inl am
      by_cases ax : a = x
      · exact Or.inr (Or.inl ax)
      · exact Or.inr (Or.inr ⟨⟨ax,au⟩,am⟩)
  have p := partition G dis
  rw [cover,erase_isolated G xa isol] at p
  exact p

private lemma ec_top [Fintype V] (G : SimpleGraph V) : ec G univ = G.edgeFinset.card := by
  classical
  have h := G.card_filter_edgeFinset_toFinset_subset (univ : Finset V)
  simpa [ec] using h.symm

omit [DecidableEq V] in
private lemma min_sum (G : SimpleGraph V) (A U : Finset V) (d : ℕ)
    (minD : ∀ a ∈ A, d ≤ (ns G U a).card) :
    A.card * d ≤ inc G A U := by
  calc
    _ = ∑ _a ∈ A, d := by simp
    _ ≤ _ := sum_le_sum minD

private lemma shell_size (G : SimpleGraph V) (U : Finset V) (x : V) (hx : x ∈ U) :
    ((U.erase x) \ ns G U x).card + (ns G U x).card + 1 = U.card := by
  have sub : ns G U x ⊆ U.erase x := fun a ha =>
    mem_erase.mpr ⟨(mem_ns.mp ha).2.ne',(mem_ns.mp ha).1⟩
  have le := card_le_card sub
  rw [card_sdiff_of_subset sub,Nat.sub_add_cancel le,card_erase_of_mem hx]
  have := card_pos.mpr ⟨x,hx⟩
  omega

private lemma add_center (G : SimpleGraph V) (S : Finset V) (x : V) (out : x ∉ S)
    (links : ∀ a ∈ S, G.Adj x a) : ec G (insert x S) = S.card + ec G S := by
  classical
  have h := partition G (A := {x}) (B := S) (by simpa using out)
  have single : ec G {x} = 0 := by
    have hh := (G.induce (({x} : Finset V) : Set V)).card_edgeFinset_le_card_choose_two
    simpa [ec] using hh
  have all : ns G (insert x S) x = S := by
    ext a
    simp only [mem_ns,mem_insert]
    exact ⟨fun ⟨hx,edge⟩ => hx.resolve_left edge.ne',fun ha => ⟨Or.inr ha,links a ha⟩⟩
  simpa [inc,single,all] using h

private lemma e_le_three (G : SimpleGraph V) (M : Finset V) (x : V)
    (out : x ∉ M) (links : ∀ a ∈ M, G.Adj x a)
    (small : ∀ S : Finset V, S.card = 5 → ec G S ≤ 7) (d : M.card ≤ 4) :
    ec G M ≤ 3 := by
  classical
  by_cases four : M.card = 4
  · have upper := small (insert x M) (by simp [four,out])
    rw [add_center G M x out links,four] at upper
    omega
  · have le : M.card ≤ 3 := by omega
    have h := (G.induce (M : Set V)).card_edgeFinset_le_card_choose_two
    have t := Nat.choose_le_choose 2 le
    change (G.induce (M : Set V)).edgeFinset.card ≤ 3
    exact h.trans ((by simpa using t : (Fintype.card (M : Set V)).choose 2 ≤ Nat.choose 3 2).trans (by decide))

private lemma shell_min (G : SimpleGraph V) (U : Finset V) (x : V) (hx : x ∈ U)
    (minD : ∀ a ∈ U, (ns G U x).card ≤ (ns G U a).card) :
    let M := ns G U x
    let A := (U.erase x) \ M
    ec G A + M.card*M.card ≤ ec G U + ec G M := by
  intro M A
  have h := shell G U x hx
  have l := min_sum G M U M.card (fun a ha => minD a (mem_ns.mp ha).1)
  change ec G U + ec G M = inc G M U + ec G A at h
  omega


omit [DecidableEq V] in
private lemma reject_five (G : SimpleGraph V) (S : Finset V) (size : S.card = 5)
    (hit : ∀ T : Finset V, T.card = 5 → 1 ≤ ec G T)
    (free : ∀ a ∈ S, ∀ b ∈ S, ¬G.Adj a b) : False := by
  classical
  have empty (a) (ha : a ∈ S) : ns G S a = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro b hb
    exact free a ha b (mem_ns.mp hb).1 (mem_ns.mp hb).2
  have n : inc G S S = 0 := sum_eq_zero fun a ha => by rw [empty a ha,card_empty]
  have := twice G S
  have := hit S size
  omega

private lemma no_five (G : SimpleGraph V) (hit : ∀ S : Finset V, S.card = 5 → 1 ≤ ec G S)
    {a b x y z : V} (size : ({a,b,x,y,z} : Finset V).card = 5)
    (ab : ¬G.Adj a b) (ax : ¬G.Adj a x) (ay : ¬G.Adj a y) (az : ¬G.Adj a z)
    (bx : ¬G.Adj b x) (by' : ¬G.Adj b y) (bz : ¬G.Adj b z)
    (xy : ¬G.Adj x y) (xz : ¬G.Adj x z) (yz : ¬G.Adj y z) : False := by
  apply reject_five G _ size hit
  intro u hu v hv
  simp only [mem_insert,mem_singleton] at hu hv
  rcases hu with rfl|rfl|rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl|rfl|rfl <;>
    simp_all [G.adj_comm]

private noncomputable def outside (G : SimpleGraph V) (S : Finset V) (x : V) :=
  (S.erase x) \ ns G S x

private lemma mem_out {G : SimpleGraph V} {x a : V} {S : Finset V} :
    a ∈ outside G S x ↔ a ∈ S ∧ a ≠ x ∧ ¬G.Adj x a := by
  simp only [outside,mem_sdiff,mem_erase,mem_ns]
  tauto

private lemma three_in_core [Fintype V] (G : SimpleGraph V)
    (hit : ∀ S : Finset V, S.card = 5 → 1 ≤ ec G S) {x y : V}
    (hy : y ∈ outside G univ x) :
    let X := outside G (outside G univ x) y
    ∀ a ∈ X, ∀ b ∈ X, ∀ d ∈ X, a ≠ b → a ≠ d → b ≠ d →
      G.Adj a b ∨ G.Adj a d ∨ G.Adj b d := by
  intro X a ha b hb d hd ab ad bd
  have info (q) (hq : q ∈ X) : q ≠ x ∧ ¬G.Adj x q ∧ q ≠ y ∧ ¬G.Adj y q :=
    ⟨(mem_out.mp (mem_out.mp hq).1).2.1,(mem_out.mp (mem_out.mp hq).1).2.2,
      (mem_out.mp hq).2.1,(mem_out.mp hq).2.2⟩
  obtain ⟨ax,exa,ay,eya⟩ := info a ha
  obtain ⟨bx,exb,by',eyb⟩ := info b hb
  obtain ⟨dx,exd,dy,eyd⟩ := info d hd
  obtain ⟨_,yx,exy⟩ := mem_out.mp hy
  by_contra! missing
  exact no_five G hit (by simp [yx.symm,ax.symm,bx.symm,dx.symm,ay.symm,by'.symm,dy.symm,ab,ad,bd] :
    ({x,y,a,b,d} : Finset V).card = 5) exy exa exb exd eya eyb eyd missing.1 missing.2.1 missing.2.2

private lemma core_dense_or_clique (G : SimpleGraph V) (X : Finset V) (size : X.card = 8)
    (tr : ∀ a ∈ X, ∀ b ∈ X, ∀ d ∈ X, a ≠ b → a ≠ d → b ≠ d →
      G.Adj a b ∨ G.Adj a d ∨ G.Adj b d) :
    16 ≤ ec G X ∨ ∃ Q ⊆ X, Q.card = 4 ∧ G.IsClique (Q : Set V) := by
  classical
  by_cases four : ∃ Q ⊆ X, Q.card = 4 ∧ G.IsClique (Q : Set V)
  · exact Or.inr four
  left
  have deg (v) (hv : v ∈ X) : 4 ≤ (ns G X v).card := by
    let B := outside G X v
    have cap : B.card ≤ 3 := by
      by_contra! big
      obtain ⟨Q,sub,c⟩ := exists_subset_card_eq big
      apply four
      refine ⟨Q,fun q hq => (mem_out.mp (sub hq)).1,c,?_⟩
      intro a ha b hb ne
      obtain ⟨aX,av,va⟩ := mem_out.mp (sub ha)
      obtain ⟨bX,bv,vb⟩ := mem_out.mp (sub hb)
      exact ((tr v hv a aX b bX av.symm bv.symm ne).resolve_left va).resolve_left vb
    have cnt := shell_size G X v hv
    change B.card + (ns G X v).card + 1 = X.card at cnt
    omega
  have le := min_sum G X X 4 deg
  rw [twice,size] at le
  omega


private lemma ec_mono [Fintype V] (G : SimpleGraph V) {A B : Finset V} (sub : A ⊆ B) :
    ec G A ≤ ec G B := by
  classical
  rw [ec,ec,← G.card_filter_edgeFinset_toFinset_subset,← G.card_filter_edgeFinset_toFinset_subset]
  apply card_le_card
  intro e he
  exact mem_filter.mpr ⟨(mem_filter.mp he).1,(mem_filter.mp he).2.trans sub⟩

private lemma split_sizes [Fintype V] (G : SimpleGraph V) (size : Fintype.card V = 17)
    (budget : ec G univ ≤ 34) (thin : ∀ S : Finset V, S.card = 5 → ec G S ≤ 7)
    (x : V) (xmin : ∀ a ∈ univ, (ns G univ x).card ≤ (ns G univ a).card)
    (y : V) (hy : y ∈ outside G univ x)
    (ymin : ∀ a ∈ outside G univ x,
      (ns G (outside G univ x) y).card ≤ (ns G (outside G univ x) a).card)
    (maxX : (outside G (outside G univ x) y).card ≤ 8) :
    let M := ns G univ x
    let A := outside G univ x
    let N := ns G A y
    let X := outside G A y
    ((M.card = 3 ∧ N.card = 4) ∨ (M.card = 4 ∧ N.card = 3)) ∧ X.card = 8 ∧ ec G X ≤ 15 := by
  classical
  intro M A N X
  have u : (univ : Finset V).card = 17 := by simp [size]
  have ca := shell_size G univ x (mem_univ x)
  change A.card + M.card + 1 = _ at ca
  rw [u] at ca
  have cx := shell_size G A y hy
  change X.card + N.card + 1 = A.card at cx
  change X.card ≤ 8 at maxX
  have hm := min_sum G univ univ M.card xmin
  rw [u,twice] at hm
  have le4 : M.card ≤ 4 := by omega
  have eM := e_le_three G M x (fun h => (mem_ns.mp h).2.ne rfl)
    (fun _ h => (mem_ns.mp h).2) thin le4
  have outer := shell_min G univ x (mem_univ x) xmin
  change ec G A + M.card*M.card ≤ ec G univ + ec G M at outer
  have inner := shell_min G A y hy ymin
  change ec G X + N.card*N.card ≤ ec G A + ec G N at inner
  have ha := min_sum G A A N.card ymin
  rw [twice] at ha
  have ea : ec G A ≤ ec G univ := ec_mono G (subset_univ _)
  have leN : N.card ≤ 4 := by
    by_contra! five
    by_cases four : M.card = 4
    · rw [four] at outer
      have ac : 12 ≤ A.card := by omega
      have := Nat.mul_le_mul ac five
      omega
    · by_cases three : M.card = 3
      · rw [three] at outer
        have ac : 13 ≤ A.card := by omega
        have := Nat.mul_le_mul ac five
        omega
      · have ac : 14 ≤ A.card := by omega
        have := Nat.mul_le_mul ac five
        omega
  have pair : (M.card = 3 ∧ N.card = 4) ∨ (M.card = 4 ∧ N.card = 3) := by
    by_cases mm : M.card = 4
    · rw [mm] at outer
      have ac : 12 ≤ A.card := by omega
      by_cases nn : 4 ≤ N.card
      · have := Nat.mul_le_mul ac nn
        omega
      · omega
    · omega
  have eN := e_le_three G N y (fun h => (mem_ns.mp h).2.ne rfl)
    (fun _ h => (mem_ns.mp h).2) thin leN
  refine ⟨pair,?_,?_⟩
  · omega
  · rcases pair with ⟨hm,hn⟩|⟨hm,hn⟩ <;> rw [hm] at outer <;> rw [hn] at inner <;> omega


private lemma clique_count [Fintype V] (G : SimpleGraph V) (T : Finset V)
    (cl : G.IsClique (T : Set V)) : (G.induce (T : Set V)).edgeFinset.card = T.card.choose 2 := by
  classical
  have eq := SimpleGraph.induce_eq_top.mpr cl
  have ce := congrArg (fun H : SimpleGraph T => Nat.card H.edgeSet) eq
  simp only [Nat.card_eq_fintype_card,card_edgeSet] at ce
  exact ce.trans (by simpa only [Fintype.card_coe] using (card_edgeFinset_top_eq_card_choose_two (V := T)))


private def Quad (G : SimpleGraph V) (Q : Finset V) : Prop :=
  Q.card = 4 ∧ G.IsClique (Q : Set V)

private lemma add_one (G : SimpleGraph V) {S : Finset V} {x : V} (out : x ∉ S) :
    ec G (insert x S) = (ns G S x).card + ec G S := by
  classical
  have h := partition G (A := {x}) (B := S) (by simpa using out)
  have one : ec G {x} = 0 := by
    have hh := (G.induce (({x} : Finset V) : Set V)).card_edgeFinset_le_card_choose_two
    simpa [ec] using hh
  have e : ns G (insert x S) x = ns G S x := by
    ext a
    simp only [mem_ns,mem_insert,or_and_right]
    constructor
    · rintro (⟨rfl,g⟩|hs)
      · exact (g.ne rfl).elim
      · exact hs
    · exact Or.inr
  simpa [inc,one,e] using h

private lemma touches [Fintype V] (G : SimpleGraph V)
    (thin : ∀ S : Finset V, S.card = 5 → ec G S ≤ 7)
    {Q : Finset V} (q : Quad G Q) {a : V} (out : a ∉ Q) : (ns G Q a).card ≤ 1 := by
  have e : ec G Q = 6 := (clique_count G Q q.2).trans (by rw [q.1]; decide)
  have bound := thin (insert a Q) (by simp [out,q.1])
  rw [add_one G out,e] at bound
  omega

-- Each forbidden vertex removes at most one point of a disjoint four-clique.
private lemma pick [Fintype V] (G : SimpleGraph V)
    (thin : ∀ S : Finset V, S.card = 5 → ec G S ≤ 7)
    {Q : Finset V} (q : Quad G Q) (F : Finset V) (few : F.card < 4)
    (out : ∀ a ∈ F, a ∉ Q) : ∃ z ∈ Q, ∀ a ∈ F, ¬G.Adj a z := by
  classical
  let covered := F.biUnion (ns G Q)
  have le : covered.card ≤ F.card := calc
    _ ≤ ∑ a ∈ F, (ns G Q a).card := card_biUnion_le
    _ ≤ ∑ _a ∈ F, 1 := sum_le_sum fun a ha => touches G thin q (out a ha)
    _ = _ := by simp
  obtain ⟨z,hz,no⟩ := exists_mem_notMem_of_card_lt_card (le.trans_lt (few.trans_eq q.1.symm))
  exact ⟨z,hz,fun a ha adj => no (mem_biUnion.mpr ⟨a,ha,mem_ns.mpr ⟨hz,adj⟩⟩)⟩

private lemma second_block [Fintype V] (G : SimpleGraph V)
    (thin : ∀ S : Finset V, S.card = 5 → ec G S ≤ 7)
    {X Q : Finset V} (size : X.card = 8) (qsub : Q ⊆ X) (q : Quad G Q)
    (tr : ∀ a ∈ X, ∀ b ∈ X, ∀ d ∈ X, a ≠ b → a ≠ d → b ≠ d →
      G.Adj a b ∨ G.Adj a d ∨ G.Adj b d) : Quad G (X \ Q) := by
  refine ⟨by rw [card_sdiff_of_subset qsub,size,q.1],?_⟩
  intro a ha b hb ab
  obtain ⟨aX,aq⟩ := mem_sdiff.mp ha
  obtain ⟨bX,bq⟩ := mem_sdiff.mp hb
  obtain ⟨z,hz,avoid⟩ := pick G thin q {a,b} (by simp [ab]) (by simpa using And.intro aq bq)
  have h := tr a aX b bX z (qsub hz) ab (fun e => aq (e ▸ hz)) (fun e => bq (e ▸ hz))
  exact h.resolve_right (not_or.mpr ⟨avoid a (by simp),avoid b (by simp)⟩)

private lemma force_exclusive_clique [Fintype V] (G : SimpleGraph V)
    (hit : ∀ S : Finset V, S.card = 5 → 1 ≤ ec G S)
    (thin : ∀ S : Finset V, S.card = 5 → ec G S ≤ 7)
    {Q R : Finset V} (q : Quad G Q) (r : Quad G R) (dis : Disjoint Q R)
    (x : V) (B : Finset V)
    (binfo : ∀ b ∈ B, b ≠ x ∧ ¬G.Adj x b ∧ b ∉ Q ∧ b ∉ R)
    (outsideX : ∀ z ∈ Q ∪ R, z ≠ x ∧ ¬G.Adj x z) : G.IsClique (B : Set V) := by
  intro a ha b hb ab
  by_contra nab
  obtain ⟨ax,xa,aq,ar⟩ := binfo a ha
  obtain ⟨bx,xb,bq,br⟩ := binfo b hb
  obtain ⟨i,hi,avoidI⟩ := pick G thin q {a,b} (by simp [ab]) (by simpa using And.intro aq bq)
  have ir := Finset.disjoint_left.mp dis hi
  have ai : a ≠ i := fun e => aq (e ▸ hi)
  have bi : b ≠ i := fun e => bq (e ▸ hi)
  obtain ⟨j,hj,avoidJ⟩ := pick G thin r {a,b,i} (by simp [ab,ai,bi])
    (by simpa using And.intro ar (And.intro br ir))
  have ij : i ≠ j := fun e => ir (e ▸ hj)
  have aj : a ≠ j := fun e => ar (e ▸ hj)
  have bj : b ≠ j := fun e => br (e ▸ hj)
  obtain ⟨ix,xi⟩ := outsideX i (mem_union_left _ hi)
  obtain ⟨jx,xj⟩ := outsideX j (mem_union_right _ hj)
  exact no_five G hit (by simp [ax.symm,bx.symm,ix.symm,jx.symm,ab,ai,aj,bi,bj,ij] :
    ({x,a,b,i,j} : Finset V).card = 5) xa xb xi xj nab (avoidI a (by simp))
    (avoidJ a (by simp)) (avoidI b (by simp)) (avoidJ b (by simp)) (avoidJ i (by simp))


-- After one representative has been chosen, its one possible external edge can
-- affect only one of the three remaining blocks. Use that block first.
private lemma finish_four [Fintype V] (G : SimpleGraph V)
    (hit : ∀ S : Finset V, S.card = 5 → 1 ≤ ec G S)
    (thin : ∀ S : Finset V, S.card = 5 → ec G S ≤ 7)
    {B C D : Finset V} (qb : Quad G B) (qc : Quad G C) (qd : Quad G D)
    (bc : Disjoint B C) (bd : Disjoint B D) (cd : Disjoint C D)
    {t a : V} (ta : t ≠ a) (eta : ¬G.Adj t a)
    (tb : t ∉ B) (tc : t ∉ C) (td : t ∉ D)
    (ab : a ∉ B) (ac : a ∉ C) (ad : a ∉ D)
    (safeC : ∀ c ∈ C, ¬G.Adj a c) (safeD : ∀ d ∈ D, ¬G.Adj a d) : False := by
  obtain ⟨b,hb,avoidB⟩ := pick G thin qb {t,a} (by simp [ta]) (by simpa using And.intro tb ab)
  have bC := Finset.disjoint_left.mp bc hb
  have bD := Finset.disjoint_left.mp bd hb
  have ntb : t ≠ b := fun e => tb (e ▸ hb)
  have nab : a ≠ b := fun e => ab (e ▸ hb)
  obtain ⟨c,hc,avoidC⟩ := pick G thin qc {t,b} (by simp [ntb]) (by simpa using And.intro tc bC)
  have cD := Finset.disjoint_left.mp cd hc
  have ntc : t ≠ c := fun e => tc (e ▸ hc)
  have nac : a ≠ c := fun e => ac (e ▸ hc)
  have nbc : b ≠ c := fun e => bC (e ▸ hc)
  obtain ⟨d,hd,avoidD⟩ := pick G thin qd {t,b,c} (by simp [ntb,ntc,nbc])
    (by simpa using And.intro td (And.intro bD cD))
  have ntd : t ≠ d := fun e => td (e ▸ hd)
  have nad : a ≠ d := fun e => ad (e ▸ hd)
  have nbd : b ≠ d := fun e => bD (e ▸ hd)
  have ncd : c ≠ d := fun e => cD (e ▸ hd)
  exact no_five G hit (by simp [ta,ntb,ntc,ntd,nab,nac,nad,nbc,nbd,ncd] :
    ({t,a,b,c,d} : Finset V).card = 5) eta (avoidB t (by simp)) (avoidC t (by simp))
    (avoidD t (by simp)) (avoidB a (by simp)) (safeC c hc) (safeD d hd)
    (avoidC b (by simp)) (avoidD b (by simp)) (avoidD c (by simp))

private lemma only_external [Fintype V] (G : SimpleGraph V)
    (lim : ∀ v, (ns G univ v).card ≤ 4) {A : Finset V} (q : Quad G A)
    {a p z : V} (ha : a ∈ A) (pa : p ∉ A) (za : z ∉ A)
    (ap : G.Adj a p) (az : G.Adj a z) : p = z := by
  classical
  by_contra ne
  have sub : insert p (insert z (A.erase a)) ⊆ ns G univ a := by
    refine insert_subset (mem_ns.mpr ⟨mem_univ _,ap⟩) (insert_subset (mem_ns.mpr ⟨mem_univ _,az⟩) ?_)
    intro b hb
    obtain ⟨ba,bA⟩ := mem_erase.mp hb
    exact mem_ns.mpr ⟨mem_univ _,q.2 ha bA ba.symm⟩
  have pOut : p ∉ A.erase a := fun e => pa (mem_of_mem_erase e)
  have zOut : z ∉ A.erase a := fun e => za (mem_of_mem_erase e)
  have count := card_le_card sub
  simp [ne,pOut,zOut,card_erase_of_mem ha,q.1] at count
  have := lim a
  omega

private lemma four_blocks [Fintype V] (G : SimpleGraph V) (size : Fintype.card V = 17)
    (hit : ∀ S : Finset V, S.card = 5 → 1 ≤ ec G S)
    (thin : ∀ S : Finset V, S.card = 5 → ec G S ≤ 7)
    (lim : ∀ v, (ns G univ v).card ≤ 4)
    (F : Fin 4 → Finset V) (quad : ∀ i, Quad G (F i))
    (dis : ∀ i j, i ≠ j → Disjoint (F i) (F j)) : False := by
  classical
  let all := univ.biUnion F
  have cap : all.card ≤ 16 := calc
    _ ≤ ∑ i, (F i).card := card_biUnion_le
    _ = ∑ _i : Fin 4, 4 := sum_congr rfl (fun i _ => (quad i).1)
    _ = _ := by simp
  obtain ⟨t,_,out⟩ := exists_mem_notMem_of_card_lt_card
    (show all.card < (univ : Finset V).card by simpa [size] using (by omega : all.card < 17))
  have notT (i : Fin 4) : t ∉ F i := fun h => out (mem_biUnion.mpr ⟨i,mem_univ _,h⟩)
  obtain ⟨a,ha,ava⟩ := pick G thin (quad 0) {t} (by simp) (by simpa using notT 0)
  have ta : t ≠ a := fun e => notT 0 (e ▸ ha)
  have notA (i : Fin 4) (i0 : i ≠ 0) : a ∉ F i := Finset.disjoint_left.mp (dis 0 i i0.symm) ha
  have arrange (i j k : Fin 4) (i0 : i ≠ 0) (j0 : j ≠ 0) (k0 : k ≠ 0)
      (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k)
      (jSafe : ∀ z ∈ F j, ¬G.Adj a z) (kSafe : ∀ z ∈ F k, ¬G.Adj a z) : False :=
    finish_four G hit thin (quad i) (quad j) (quad k) (dis _ _ ij) (dis _ _ ik) (dis _ _ jk)
      ta (ava t (by simp)) (notT i) (notT j) (notT k) (notA i i0) (notA j j0) (notA k k0) jSafe kSafe
  have spare {i j : Fin 4} (i0 : i ≠ 0) (j0 : j ≠ 0) (ij : i ≠ j)
      (seen : ∃ w ∈ F i, G.Adj a w) : ∀ z ∈ F j, ¬G.Adj a z := by
    obtain ⟨w,hw,aw⟩ := seen
    intro z hz az
    have eq := only_external G lim (quad 0) ha (Finset.disjoint_left.mp (dis _ _ i0) hw)
      (Finset.disjoint_left.mp (dis _ _ j0) hz) aw az
    exact Finset.disjoint_left.mp (dis _ _ ij) hw (eq ▸ hz)
  by_cases b : ∃ w ∈ F 1, G.Adj a w
  · exact arrange 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (spare (by decide) (by decide) (by decide) b) (spare (by decide) (by decide) (by decide) b)
  push Not at b
  by_cases c : ∃ w ∈ F 2, G.Adj a w
  · exact arrange 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) b
      (spare (by decide) (by decide) (by decide) c)
  push Not at c
  exact arrange 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) b c


private noncomputable def core [Fintype V] (G : SimpleGraph V) (x y : V) :=
  outside G (outside G univ x) y

private lemma core_sym [Fintype V] (G : SimpleGraph V) (x y : V) : core G x y = core G y x := by
  ext z
  simp only [core,mem_out,mem_univ,true_and]
  tauto

private noncomputable def group [Fintype V] (G : SimpleGraph V) (x y : V) :=
  insert y (ns G (outside G univ x) y)

private lemma group_info [Fintype V] {G : SimpleGraph V} {x y z : V} (hy : y ∈ outside G univ x)
    (hz : z ∈ group G x y) : z ∈ outside G univ x ∧ (z = y ∨ G.Adj y z) := by
  rcases mem_insert.mp hz with rfl|h
  · exact ⟨hy,Or.inl rfl⟩
  · exact ⟨(mem_ns.mp h).1,Or.inr (mem_ns.mp h).2⟩

private lemma group_core [Fintype V] {G : SimpleGraph V} {x y : V} (hy : y ∈ outside G univ x) :
    Disjoint (group G x y) (core G x y) := by
  apply Finset.disjoint_left.mpr
  intro z hz zin
  have h := (mem_out.mp zin).2
  exact (group_info hy hz).2.elim h.1 h.2

private lemma swap_out [Fintype V] {G : SimpleGraph V} {x y : V} (hy : y ∈ outside G univ x) :
    x ∈ outside G univ y := mem_out.mpr ⟨mem_univ _,(mem_out.mp hy).2.1.symm,
      fun e => (mem_out.mp hy).2.2 e.symm⟩

private lemma group_disjoint [Fintype V] {G : SimpleGraph V} {x y : V} (hy : y ∈ outside G univ x) :
    Disjoint (group G x y) (group G y x) := by
  apply Finset.disjoint_left.mpr
  intro z hz zw
  have h := (mem_out.mp (group_info (swap_out hy) zw).1).2
  exact (group_info hy hz).2.elim h.1 h.2

private lemma group_is_clique [Fintype V] (G : SimpleGraph V)
    (hit : ∀ S : Finset V, S.card = 5 → 1 ≤ ec G S)
    (thin : ∀ S : Finset V, S.card = 5 → ec G S ≤ 7)
    {x y : V} (Q R : Finset V) (q : Quad G Q) (r : Quad G R) (dis : Disjoint Q R)
    (qsub : Q ⊆ core G x y) (rsub : R ⊆ core G x y) : G.IsClique (group G x y : Set V) := by
  let B := ns G (outside G univ x) y
  have cl : G.IsClique (B : Set V) := by
    apply force_exclusive_clique G hit thin q r dis x
    · intro b hb
      obtain ⟨side,yb⟩ := mem_ns.mp hb
      obtain ⟨_,bx,xb⟩ := mem_out.mp side
      exact ⟨bx,xb,fun h => (mem_out.mp (qsub h)).2.2 yb,
        fun h => (mem_out.mp (rsub h)).2.2 yb⟩
    · intro z hz
      have h := (mem_union.mp hz).elim (qsub ·) (rsub ·)
      exact (mem_out.mp (mem_out.mp h).1).2
  intro a ha b hb ne
  rcases mem_insert.mp ha with rfl|ha <;> rcases mem_insert.mp hb with rfl|hb
  · exact (ne rfl).elim
  · exact (mem_ns.mp hb).2
  · exact (mem_ns.mp ha).2.symm
  · exact cl ha hb ne

private lemma clique_limit [Fintype V] (G : SimpleGraph V)
    (thin : ∀ S : Finset V, S.card = 5 → ec G S ≤ 7) (S : Finset V)
    (cl : G.IsClique (S : Set V)) : S.card ≤ 4 := by
  by_contra! big
  obtain ⟨T,sub,five⟩ := exists_subset_card_eq big
  have tcl : G.IsClique (T : Set V) := fun _ ha _ hb ne => cl (sub ha) (sub hb) ne
  have count : ec G T = 10 := (clique_count G T tcl).trans (by rw [five]; decide)
  have := thin T five
  omega

omit [DecidableEq V] in
private lemma caps [Fintype V] (G : SimpleGraph V) (size : Fintype.card V = 17)
    (budget : ec G univ ≤ 34) (lower : ∀ v, 4 ≤ (ns G univ v).card) :
    ∀ v, (ns G univ v).card = 4 := by
  have h : (∑ _v : V, 4) = inc G univ univ := by
    have lhs : (∑ _v : V, 4) = 68 := by simp [size]
    have lo := min_sum G univ univ 4 (fun a _ => lower a)
    simp only [card_univ,size] at lo
    have := twice G (univ : Finset V)
    omega
  have equal := (sum_eq_sum_iff_of_le (s := (univ : Finset V)) (f := fun _ => 4)
    (g := fun a => (ns G univ a).card) (fun a _ => lower a)).mp h
  exact fun v => (equal v (mem_univ v)).symm

private lemma disjoint_four [Fintype V] (G : SimpleGraph V) (size : Fintype.card V = 17)
    (hit : ∀ S : Finset V, S.card = 5 → 1 ≤ ec G S)
    (thin : ∀ S : Finset V, S.card = 5 → ec G S ≤ 7)
    (lim : ∀ v, (ns G univ v).card ≤ 4)
    {A B C D : Finset V} (a : Quad G A) (b : Quad G B) (c : Quad G C) (d : Quad G D)
    (ab : Disjoint A B) (ac : Disjoint A C) (ad : Disjoint A D)
    (bc : Disjoint B C) (bd : Disjoint B D) (cd : Disjoint C D) : False := by
  apply four_blocks G size hit thin lim ![A,B,C,D]
  · intro i
    fin_cases i <;> first | exact a | exact b | exact c | exact d
  · intro i j ne
    fin_cases i <;> fin_cases j <;> first
      | exact (ne rfl).elim
      | assumption
      | apply Disjoint.symm; assumption


-- Take two successive minimum-degree vertices. Their common nonneighbors
-- form an eight-vertex graph that would have at most fifteen edges.
private theorem large [Fintype V] (G : SimpleGraph V) (size : Fintype.card V = 17)
    (every : ∀ S : Finset V, S.card = 5 → 1 ≤ ec G S ∧ ec G S ≤ 7)
    (common : ∀ x y, x ≠ y → ¬G.Adj x y →
      (univ.filter (fun z => z ≠ x ∧ z ≠ y ∧ ¬G.Adj x z ∧ ¬G.Adj y z)).card ≤ 8) :
    35 ≤ G.edgeFinset.card := by
  classical
  by_contra! few
  have budget : ec G univ ≤ 34 := by rw [ec_top]; omega
  have hit (S : Finset V) (hs : S.card = 5) := (every S hs).1
  have thin (S : Finset V) (hs : S.card = 5) := (every S hs).2
  have u : (univ : Finset V).card = 17 := by simp [size]
  obtain ⟨x,hx,xmin⟩ := exists_min_image univ (fun a => (ns G univ a).card)
    (card_pos.mp (by omega : 0 < (univ : Finset V).card))
  let M := ns G univ x
  let A := outside G univ x
  have m := min_sum G univ univ M.card xmin
  rw [u,twice] at m
  have ca := shell_size G univ x hx
  change A.card + M.card + 1 = _ at ca
  rw [u] at ca
  obtain ⟨y,hy,ymin⟩ := exists_min_image A (fun a => (ns G A a).card)
    (card_pos.mp (by omega : 0 < A.card))
  let N := ns G A y
  let X := core G x y
  have yx := (mem_out.mp hy).2.1
  have xy := (mem_out.mp hy).2.2
  have bound := common x y yx.symm xy
  have eq : X = univ.filter (fun z => z ≠ x ∧ z ≠ y ∧ ¬G.Adj x z ∧ ¬G.Adj y z) := by
    ext z
    simp only [X,core,mem_out,mem_filter,mem_univ,true_and]
    tauto
  have mx : X.card ≤ 8 := by
    rw [eq]
    convert! bound using 1
  obtain ⟨orders,eight,small⟩ := split_sizes G size budget thin x xmin y hy ymin mx
  change (M.card = 3 ∧ N.card = 4) ∨ (M.card = 4 ∧ N.card = 3) at orders
  change X.card = 8 at eight
  change ec G X ≤ 15 at small
  have tr := three_in_core G hit hy
  rcases core_dense_or_clique G X eight tr with many|⟨Q,qsub,four,cl⟩
  · omega
  have quad : Quad G Q := ⟨four,cl⟩
  let R := X \ Q
  have rsub : R ⊆ X := sdiff_subset
  have red : Quad G R := second_block G thin eight qsub quad tr
  have dis : Disjoint Q R := Finset.disjoint_left.mpr (fun _ ha hb => (mem_sdiff.mp hb).2 ha)
  have clY := group_is_clique G hit thin Q R quad red dis qsub rsub
  have outY : y ∉ N := fun h => (mem_ns.mp h).2.ne rfl
  have numY : (group G x y).card = N.card+1 := card_insert_of_notMem outY
  have yBound := clique_limit G thin (group G x y) clY
  rcases orders with ⟨_,n4⟩|⟨m4,n3⟩
  · omega
  have reg := caps G size budget (fun a => m4 ▸ xmin a (mem_univ a))
  have hx' := swap_out hy
  have symm : X = core G y x := core_sym G x y
  have clX := group_is_clique G hit thin Q R quad red dis (symm ▸ qsub) (symm ▸ rsub)
  have s1 := shell_size G univ y (mem_univ y)
  change (outside G univ y).card + (ns G univ y).card + 1 = _ at s1
  rw [reg,u] at s1
  have s2 := shell_size G (outside G univ y) x hx'
  change (core G y x).card + (ns G (outside G univ y) x).card + 1 = _ at s2
  rw [← symm,eight] at s2
  have xOut : x ∉ ns G (outside G univ y) x := fun h => (mem_ns.mp h).2.ne rfl
  have numX : (group G y x).card = (ns G (outside G univ y) x).card+1 := card_insert_of_notMem xOut
  have dY := group_core hy
  have dX := group_core hx'
  rw [← symm] at dX
  exact disjoint_four G size hit thin (fun v => (reg v).le)
    ⟨by omega,clY⟩ ⟨by omega,clX⟩ quad red (group_disjoint hy)
    (dY.mono_right qsub) (dY.mono_right rsub) (dX.mono_right qsub) (dX.mono_right rsub) dis

end OMA.SeventeenVertices


/- # Four colors on seventeen vertices
The minority-color argument follows Lemma 2 of Erdős and Gyárfás,
*Split and balanced colorings of complete graphs* (1999).
-/
namespace OMA.Erdos617R4
open Finset SimpleGraph
open scoped Classical

private def graph {V : Type} (c : Sym2 V → Fin 4) (k : Fin 4) : SimpleGraph V where
  Adj u v := u ≠ v ∧ c s(u,v) = k
  symm := ⟨fun _ _ ⟨h,e⟩ => ⟨h.symm,Sym2.eq_swap ▸ e⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private lemma class_edges {V : Type} [Fintype V] (c : Sym2 V → Fin 4) (k : Fin 4) :
    (graph c k).edgeFinset = (⊤ : SimpleGraph V).edgeFinset.filter (fun e => c e = k) := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
    rw [mem_filter, mem_edgeFinset, mem_edgeFinset]
    exact Iff.rfl

private lemma edge_total {V : Type} [Fintype V] (c : Sym2 V → Fin 4) :
    ∑ k, (graph c k).edgeFinset.card = (Fintype.card V).choose 2 := by
  simp_rw [class_edges]
  rw [sum_card_fiberwise_eq_card_filter]
  simpa using (card_edgeFinset_top_eq_card_choose_two (V := V))

private def Witness {V : Type} (c : Sym2 V → Fin 4) : Prop :=
  ∃ (S : Finset V) (k : Fin 4), S.card = 5 ∧
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b → c s(a,b) ≠ k

/-- In a coloring without a witness, each color occupies one to seven of
the ten edges on every set of five vertices. -/
private lemma five_edges {V : Type} [DecidableEq V] (c : Sym2 V → Fin 4) (h : ¬ Witness c)
    (S : Finset V) (five : S.card = 5) (k : Fin 4) :
    1 ≤ ((graph c k).induce (S : Set V)).edgeFinset.card ∧
      ((graph c k).induce (S : Set V)).edgeFinset.card ≤ 7 := by
  classical
  let d : Sym2 S → Fin 4 := c ∘ Sym2.map Subtype.val
  have eq (i : Fin 4) : (graph c i).induce (S : Set V) = graph d i := by
    ext a b
    change ((a : V) ≠ b ∧ _) ↔ (a ≠ b ∧ _)
    constructor
    · rintro ⟨ne,col⟩
      exact ⟨fun e => ne (congrArg Subtype.val e),col⟩
    · rintro ⟨ne,col⟩
      exact ⟨fun e => ne (Subtype.ext e),col⟩
  have pos (i : Fin 4) : 0 < (graph d i).edgeFinset.card := by
    by_contra! empty
    apply h
    refine ⟨S,i,five,?_⟩
    intro a ha b hb ne ab
    have adj : (graph d i).Adj ⟨a,ha⟩ ⟨b,hb⟩ :=
      ⟨fun e => ne (congrArg Subtype.val e), ab⟩
    have mem : s(⟨a,ha⟩,⟨b,hb⟩) ∈ (graph d i).edgeFinset := mem_edgeFinset.mpr adj
    have := card_pos.mpr ⟨_,mem⟩
    omega
  have total := edge_total d
  rw [Fintype.card_coe,five] at total
  simp only [Fin.sum_univ_four] at total
  norm_num [Nat.choose] at total
  have ce := congrArg (fun H : SimpleGraph S => Nat.card H.edgeSet) (eq k)
  change Nat.card _ = Nat.card _ at ce
  simp only [Nat.card_eq_fintype_card, card_edgeSet] at ce
  rw [ce]
  refine ⟨pos k,?_⟩
  have p0 := pos 0
  have p1 := pos 1
  have p2 := pos 2
  have p3 := pos 3
  rcases (by decide : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) k with rfl|rfl|rfl|rfl <;> omega

/-- The common nonneighbors of two distinct vertices, excluding the vertices
themselves. -/
private noncomputable def outsidePair {V : Type} [Fintype V] (G : SimpleGraph V) (x y : V) : Finset V :=
  univ.filter fun z => z ≠ x ∧ z ≠ y ∧ ¬G.Adj x z ∧ ¬G.Adj y z

private lemma mem_outsidePair {V : Type} [Fintype V] {G : SimpleGraph V} {x y z : V} :
    z ∈ outsidePair G x y ↔ z ≠ x ∧ z ≠ y ∧ ¬G.Adj x z ∧ ¬G.Adj y z := by
  simp [outsidePair]

private lemma no_empty_triple {V : Type} [Fintype V] [DecidableEq V]
    {c : Sym2 V → Fin 4} (bad : ¬ Witness c) (k : Fin 4) {x y : V}
    (xy : x ≠ y) (exy : ¬(graph c k).Adj x y) :
    ∀ a ∈ outsidePair (graph c k) x y, ∀ b ∈ outsidePair (graph c k) x y,
      ∀ d ∈ outsidePair (graph c k) x y, a ≠ b → a ≠ d → b ≠ d →
        (graph c k).Adj a b ∨ (graph c k).Adj a d ∨ (graph c k).Adj b d := by
  intro a ha b hb d hd ab ad bd
  obtain ⟨ax,ay,exa,eya⟩ := mem_outsidePair.mp ha
  obtain ⟨bx,by',exb,eyb⟩ := mem_outsidePair.mp hb
  obtain ⟨dx,dy,exd,eyd⟩ := mem_outsidePair.mp hd
  by_contra! edges
  obtain ⟨eab,ead,ebd⟩ := edges
  apply bad
  refine ⟨{x,y,a,b,d},k,by simp [xy,ax.symm,ay.symm,bx.symm,by'.symm,dx.symm,dy.symm,ab,ad,bd],?_⟩
  have diff {s t : V} (ne : s ≠ t) (e : ¬(graph c k).Adj s t) : c s(s,t) ≠ k :=
    fun same => e ⟨ne,same⟩
  have := diff xy exy
  have hxA := diff ax.symm exa
  have hxB := diff bx.symm exb
  have hxD := diff dx.symm exd
  have hyA := diff ay.symm eya
  have hyB := diff by'.symm eyb
  have hyD := diff dy.symm eyd
  have hab := diff ab eab
  have had := diff ad ead
  have hbd := diff bd ebd
  clear ha hb hd exy exa eya exb eyb exd eyd eab ead ebd
  intro u hu v hv ne
  simp only [mem_insert,mem_singleton] at hu hv
  rcases hu with rfl|rfl|rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl|rfl|rfl <;>
    simp_all [Sym2.eq_swap]

/-- Local Ramsey step. Nine vertices without an independent triple contain
five vertices spanning at least eight edges. -/
private def H1 : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (X : Finset V), 9 ≤ X.card →
    (∀ a ∈ X, ∀ b ∈ X, ∀ d ∈ X, a ≠ b → a ≠ d → b ≠ d →
      G.Adj a b ∨ G.Adj a d ∨ G.Adj b d) →
    ∃ S ⊆ X, S.card = 5 ∧ 8 ≤ (G.induce (S : Set V)).edgeFinset.card

/-- The remaining extremal counting step on seventeen vertices. If every
five-set spans between one and seven edges and each independent pair has at most
eight common nonneighbors, the graph needs at least thirty-five edges. -/
private def H2 : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    Fintype.card V = 17 →
    (∀ S : Finset V, S.card = 5 → 1 ≤ (G.induce (S : Set V)).edgeFinset.card ∧
      (G.induce (S : Set V)).edgeFinset.card ≤ 7) →
    (∀ x y, x ≠ y → ¬G.Adj x y →
      (univ.filter (fun z => z ≠ x ∧ z ≠ y ∧ ¬G.Adj x z ∧ ¬G.Adj y z)).card ≤ 8) →
    35 ≤ G.edgeFinset.card

private theorem main : H1 → H2 → type_of% @Erdos617.erdos_617.variants.r_eq_4 := by
  intro localBound globalBound _ _ V _ _ size c
  classical
  change Witness c
  by_contra bad
  have order : Fintype.card V = 17 := by simpa using size
  have total := edge_total c
  rw [order] at total
  simp only [Fin.sum_univ_four] at total
  norm_num [Nat.choose] at total
  obtain ⟨k,minor⟩ : ∃ k : Fin 4, (graph c k).edgeFinset.card ≤ 34 := by
    by_contra! all
    have h0 := all 0
    have h1 := all 1
    have h2 := all 2
    have h3 := all 3
    omega
  have five (S : Finset V) (hs : S.card = 5) := five_edges c bad S hs k
  apply Nat.not_succ_le_self 34
  apply le_trans (globalBound (graph c k) order five ?_) minor
  intro x y xy nonedge
  by_contra! nine
  let Z := univ.filter (fun z => z ≠ x ∧ z ≠ y ∧ ¬(graph c k).Adj x z ∧ ¬(graph c k).Adj y z)
  change 8 < Z.card at nine
  have zeq : Z = outsidePair (graph c k) x y := by ext z; simp [Z, outsidePair]
  rw [zeq] at nine
  have bound : 9 ≤ (outsidePair (graph c k) x y).card := by omega
  obtain ⟨S,_,hs,dense⟩ := localBound (graph c k) _ bound (no_empty_triple bad k xy nonedge)
  have upper := (five S hs).2
  omega

end OMA.Erdos617R4

theorem OMA.solution : type_of% @Erdos617.erdos_617.variants.r_eq_4 :=
  OMA.Erdos617R4.main
    (fun G X size h => OMA.FourColorLocal.localRamsey G X size h)
    (fun G size every common => OMA.SeventeenVertices.large G size every common)
