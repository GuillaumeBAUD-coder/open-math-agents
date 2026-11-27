import FormalConjectures.WrittenOnTheWallII.GraphConjecture372

/-!
A minimum cover by at most two paths leaves at most one tree edge outside
those paths. Remove that edge and choose the bipartitions of the components
so that its endpoints have the same color. The resulting color classes
permit an incidence count against a minimum total dominating set.

The case split on the path cover number is due to @jagong-cmu. The
two-path counting argument and the general edge-count bound are formalized
by @Deldor14.
-/

namespace OMA.TwoPaths
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {T : SimpleGraph V}

private lemma min_path_cover (T : SimpleGraph V) :
    ∃ P : Finset (Finset V), P.card = T.pathCoverNumber ∧ T.IsPathCover P := by
  apply Nat.sInf_mem (s := {k : Nat | ∃ P : Finset (Finset V), P.card = k ∧ T.IsPathCover P})
  let U := (univ : Finset V).image (fun v => {v} : V → Finset V)
  refine ⟨U.card,U,rfl,?_,?_,?_⟩
  · intro s hs t ht h
    obtain ⟨u,_,rfl⟩ := mem_image.mp hs
    obtain ⟨v,_,rfl⟩ := mem_image.mp ht
    simpa using h
  · intro v _
    exact mem_biUnion.mpr ⟨{v},mem_image_of_mem _ (mem_univ v),mem_singleton_self _⟩
  · intro s hs
    obtain ⟨u,_,rfl⟩ := mem_image.mp hs
    exact ⟨u,u,.nil,by simp,by simp⟩

/-- A vertex on a simple path has at most a predecessor and a successor. -/
private lemma path_deg {a b : V} (p : T.Walk a b) (hp : p.IsPath) (v : V) :
    p.toSubgraph.spanningCoe.degree v ≤ 2 := by
  classical
  by_cases vmem : v ∈ p.support
  · obtain ⟨i,hi,hv⟩ := List.mem_iff_getElem.mp vmem
    have il : i ≤ p.length := by simpa using hi
    have ie : p.getVert i = v := by simpa [p.getVert_eq_support_getElem il] using hv
    have sub : p.toSubgraph.spanningCoe.neighborFinset v ⊆
        {p.getVert (i-1),p.getVert (i+1)} := by
      intro w hw
      obtain ⟨j,eq,hjl⟩ := p.toSubgraph_adj_iff.mp ((mem_neighborFinset _ _ _).mp hw)
      rcases Sym2.eq_iff.mp eq with ⟨e,f⟩ | ⟨e,f⟩
      · have ji : j=i := hp.getVert_injOn (show j ≤ p.length by omega) il (e.trans ie.symm)
        subst j; simp [f]
      · have ji : j+1=i := hp.getVert_injOn (show j+1 ≤ p.length by omega) il (f.trans ie.symm)
        subst i; simp [e]
    exact (card_le_card sub).trans (card_le_two)
  · have zero : p.toSubgraph.spanningCoe.neighborFinset v = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro u h
      have h' : p.toSubgraph.Adj v u := (mem_neighborFinset _ _ _).mp h
      exact vmem (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert h'))
    rw [← card_neighborFinset_eq_degree,zero]
    simp

/-- The paths in a cover of size at most two contain all but at most one tree edge. -/
private lemma linear_forest (T : SimpleGraph V) (tree : T.IsTree) (hc : T.pathCoverNumber ≤ 2) :
    ∃ (J : SimpleGraph V) (_ : DecidableRel J.Adj), J ≤ T ∧ (∀ v, J.degree v ≤ 2) ∧
      (T.edgeFinset \ J.edgeFinset).card ≤ 1 := by
  classical
  obtain ⟨P,size,dis,cov,hpaths⟩ := min_path_cover T
  choose a b p simple verts using fun s : P => hpaths s s.property
  let J := ⨆ s : P, (p s).toSubgraph.spanningCoe
  have adj {x y : V} : J.Adj x y ↔ ∃ s : P, (p s).toSubgraph.Adj x y := by
    simp [J,iSup_adj]
  have le : J ≤ T := by
    intro x y h
    obtain ⟨s,hs⟩ := adj.mp h
    exact (p s).toSubgraph.adj_sub hs
  have unique {v : V} {s t : P} (hs : v ∈ s.val) (ht : v ∈ t.val) : s=t := by
    by_contra ne
    exact disjoint_left.mp (dis s s.property t t.property (fun e => ne (Subtype.ext e))) hs ht
  refine ⟨J,inferInstance,le,?_,?_⟩
  · intro v
    obtain ⟨s,hs,vs⟩ := mem_biUnion.mp (cov (mem_univ v))
    let t : P := ⟨s,hs⟩
    have hsub : J.neighborFinset v ⊆ (p t).toSubgraph.spanningCoe.neighborFinset v := by
      intro w hw
      obtain ⟨u,hu⟩ := adj.mp ((mem_neighborFinset _ _ _).mp hw)
      have vmem : v ∈ u.val := by
        rw [verts]; exact List.mem_toFinset.mpr ((p u).mem_verts_toSubgraph.mp ((p u).toSubgraph.edge_vert hu))
      have e : u = t := unique vmem vs
      subst u
      exact (mem_neighborFinset _ _ _).mpr hu
    exact (card_le_card hsub).trans (path_deg _ (simple t) v)
  · let F (s : P) := (p s).edges.toFinset
    have es : J.edgeFinset = univ.biUnion F := by
      ext e
      induction e using Sym2.inductionOn with
      | _ x y =>
        simp only [mem_edgeFinset,mem_biUnion,mem_univ,true_and, mem_edgeSet,adj,F,List.mem_toFinset]
        exact exists_congr fun s => (p s).adj_toSubgraph_iff_mem_edges
    have dF : (↑(univ : Finset P) : Set P).PairwiseDisjoint F := by
      intro s _ t _ ne
      apply Finset.disjoint_left.mpr
      intro e hs ht
      induction e using Sym2.inductionOn with
      | _ x y =>
        have mem (i : P) (h : s(x,y) ∈ F i) : x ∈ i.val := by
          rw [verts]
          exact List.mem_toFinset.mpr ((p i).fst_mem_support_of_mem_edges (List.mem_toFinset.mp h))
        exact ne (unique (mem s hs) (mem t ht))
    have dS : (↑(univ : Finset P) : Set P).PairwiseDisjoint (fun s => s.val) := by
      intro s _ t _ ne
      exact dis s s.property t t.property (fun e => ne (Subtype.ext e))
    have all : (univ.biUnion fun s : P => s.val) = (univ : Finset V) := by
      apply eq_univ_of_forall
      intro v
      obtain ⟨s,hs,hv⟩ := mem_biUnion.mp (cov (mem_univ v))
      exact mem_biUnion.mpr ⟨⟨s,hs⟩,mem_univ _,hv⟩
    have sz (s : P) : (F s).card + 1 = s.val.card := by
      rw [verts]; simp [F,List.toFinset_card_of_nodup (simple s).edges_nodup,
        List.toFinset_card_of_nodup (simple s).support_nodup]
    have hsum := Finset.sum_congr (s₁ := (univ : Finset P)) rfl (fun s _ => sz s)
    rw [sum_add_distrib, ← card_biUnion dF, ← card_biUnion dS, all, ← es] at hsum
    simp only [card_univ,sum_const,smul_eq_mul,mul_one,Fintype.card_coe] at hsum
    have ec := tree.card_edgeFinset
    rw [card_sdiff_of_subset (edgeFinset_mono le)]
    omega

private noncomputable def nbs (T : SimpleGraph V) (v : V) (S : Finset V) := S.filter (T.Adj v)
private noncomputable def inc (T : SimpleGraph V) (A B : Finset V) := ∑ a ∈ A, (nbs T a B).card
omit [Fintype V] [DecidableEq V] in
private lemma inc_sym (T : SimpleGraph V) (A B : Finset V) : inc T A B = inc T B A := by
  classical
  calc
    _ = ∑ a ∈ A, ∑ b ∈ B, (if T.Adj a b then 1 else 0 : ℕ) := by simp [inc,nbs]
    _ = ∑ b ∈ B, ∑ a ∈ A, (if T.Adj a b then 1 else 0 : ℕ) := sum_comm
    _ = _ := by simp [inc,nbs,T.adj_comm]

omit [Fintype V] [DecidableEq V] in
private lemma cover_bound {S : Finset V} (h : T.IsVertexCover S) : T.vertexCoverNum.toNat ≤ S.card :=
  ENat.toNat_le_of_le_natCast (by simpa using h.vertexCoverNum_le)

private lemma twice (T : SimpleGraph V) (tree : T.IsTree) :
    2*T.vertexCoverNum.toNat ≤ Fintype.card V := by
  classical
  obtain ⟨c⟩ := tree.colorable_two
  let U (k : Fin 2) := univ.filter (fun v => c v = k)
  have cv (k : Fin 2) : T.IsVertexCover (U k) := by
    intro v w vw
    have h := c.valid vw
    change v ∈ U k ∨ w ∈ U k
    simp only [U,mem_filter,mem_univ,true_and]
    omega
  have ha := cover_bound (cv 0)
  have hb := cover_bound (cv 1)
  have sum : ∑ k, (U k).card = Fintype.card V := by
    simpa [U] using (sum_card_fiberwise_eq_card_filter (s := univ) (t := univ) (g := fun v => c v))
  simp only [Fin.sum_univ_two] at sum
  omega

private lemma counting (T : SimpleGraph V) (tree : T.IsTree)
    (D R : Finset V) (dom : T.IsTotalDominating D) (x y : V) (xy : x ≠ y)
    (xr : x∈R) (yr : y∈R)
    (noB : ∀ v ∉ R, ∀ w ∉ R, ¬ T.Adj v w)
    (except : ∀ v ∈ R, ∀ w ∈ R, T.Adj v w → (v=x ∧ w=y) ∨ (v=y ∧ w=x))
    (dR : ∀ v ∈ R, (nbs T v Rᶜ).card ≤ 2)
    (dB : ∀ v ∉ R, (nbs T v R).card ≤ 2) :
    T.vertexCoverNum.toNat ≤ D.card := by
  classical
  let B := Rᶜ
  let A := D ∩ R
  let C := D ∩ B
  let Q : Finset V := {x,y}
  have qc : Q.card = 2 := card_pair xy
  have qr : Q ⊆ R := by
    intro z hz
    rcases (show z=x ∨ z=y by simpa [Q] using hz) with rfl | rfl <;> assumption
  have parts : A.card + C.card = D.card := by
    dsimp [A,C,B]
    rw [← card_union_of_disjoint (by apply Finset.disjoint_left.mpr; simp [mem_inter]; tauto)]
    congr 1
    ext z
    simp; tauto
  have total : R.card+B.card = Fintype.card V := by dsimp [B]; rw [card_compl]; have := card_le_univ R; omega
  have isCover : T.IsVertexCover R := by
    intro v w h
    by_contra! bad
    exact noB v bad.1 w bad.2 h
  by_contra! bad
  have tr := twice T tree
  have small : D.card < R.card := lt_of_lt_of_le bad (cover_bound isCover)
  have preB (v) (hv : v∈B) : 1 ≤ (nbs T v A).card := by
    obtain ⟨w,hw,h⟩ := dom v
    have wr : w ∈ R := by by_contra ww; exact noB v (mem_compl.mp hv) w ww h
    exact card_pos.mpr ⟨w,mem_filter.mpr ⟨mem_inter.mpr ⟨hw,wr⟩,h⟩⟩
  have preR (v) (hv : v∈R) : (if v∈Q then 0 else 1) ≤ (nbs T v C).card := by
    split
    · omega
    · rename_i hn
      obtain ⟨w,hw,h⟩ := dom v
      have wb : w ∉ R := by
        intro wr
        rcases except _ hv _ wr h with ⟨vx,_⟩ | ⟨vy,_⟩ <;> simp_all [Q]
      exact card_pos.mpr ⟨w,mem_filter.mpr ⟨mem_inter.mpr ⟨hw,mem_compl.mpr wb⟩,h⟩⟩
  have br := sum_le_sum preB
  have rr := sum_le_sum preR
  have capB : inc T B A ≤ 2*A.card := by
    rw [inc_sym]; unfold inc
    calc
      _ ≤ ∑ _ ∈ A, 2 := sum_le_sum (fun v hv => dR _ (mem_inter.mp hv).2)
      _ = _ := by simp [Nat.mul_comm]
  have capR : inc T R C ≤ 2*C.card := by
    rw [inc_sym]; unfold inc
    calc
      _ ≤ ∑ _ ∈ C, 2 := sum_le_sum (fun v hv => dB _ (mem_compl.mp (mem_inter.mp hv).2))
      _ = _ := by simp [Nat.mul_comm]
  have sumR : (∑ v ∈ R, (if v∈Q then 0 else 1 : Nat)) = R.card-2 := by
    rw [sum_ite]
    simp [card_sdiff_of_subset qr,qc,filter_notMem_eq_sdiff]
  have sumB : (∑ _ ∈ B, (1 : Nat)) = B.card := by simp
  have sumR' : R.card-2 ≤ inc T R C := by simpa only [sumR,inc] using rr
  have sumB' : B.card ≤ inc T B A := by simpa only [sumB,inc] using br
  have qr' := card_le_card qr
  have eqB : (∑ _ ∈ B, (1 : Nat)) = inc T B A := by omega
  have eqR : (∑ v ∈ R, (if v∈Q then 0 else 1 : Nat)) = inc T R C := by omega
  -- Both incidence bounds are tight. Every blue vertex has exactly one
  -- red dominator and the two exceptional red vertices have no blue dominator.
  have satB := (sum_eq_sum_iff_of_le preB).mp eqB
  have satR := (sum_eq_sum_iff_of_le preR).mp eqR
  have exD (v) (hq : v∈Q) : v∈D := by
    rcases (show v=x ∨ v=y by simpa [Q] using hq) with rfl | rfl
    · obtain ⟨w,hw,h⟩ := dom y
      have empty := satR y yr
      simp [Q] at empty
      by_cases wr : w∈R
      · rcases except y yr w wr h with p | p
        · exact (xy p.1.symm).elim
        · exact p.2 ▸ hw
      · have hm : w∈nbs T y C := mem_filter.mpr ⟨mem_inter.mpr ⟨hw,mem_compl.mpr wr⟩,h⟩
        have pos : 0 < (nbs T y C).card := card_pos.mpr ⟨w,hm⟩
        omega
    · obtain ⟨w,hw,h⟩ := dom x
      have empty := satR x xr
      simp [Q] at empty
      by_cases wr : w∈R
      · rcases except x xr w wr h with p | p
        · exact p.2 ▸ hw
        · exact (xy p.1).elim
      · have hm : w∈nbs T x C := mem_filter.mpr ⟨mem_inter.mpr ⟨hw,mem_compl.mpr wr⟩,h⟩
        have pos : 0 < (nbs T x C).card := card_pos.mpr ⟨w,hm⟩
        omega
  have qa : Q ⊆ A := fun v hv => mem_inter.mpr ⟨exD v hv,qr hv⟩
  -- Count the edges between the two parts of the dominating set in both directions.
  have c1 : inc T C A = C.card := by
    unfold inc
    calc
      _ = ∑ _ ∈ C, 1 := sum_congr rfl (fun v hv => (satB v (mem_inter.mp hv).2).symm)
      _ = _ := by simp
  have c2 : inc T A C = A.card-2 := by
    unfold inc
    calc
      _ = ∑ v ∈ A, (if v∈Q then 0 else 1 : Nat) :=
        sum_congr rfl (fun v hv => (satR v (mem_inter.mp hv).2).symm)
      _ = _ := by rw [sum_ite]; simp [card_sdiff_of_subset qa,qc,filter_notMem_eq_sdiff]
  have cy := inc_sym T A C
  have qa' := card_le_card qa
  omega

private lemma join_parts (T : SimpleGraph V) (tree : T.IsTree) (hn : 2 ≤ Fintype.card V)
    (hc : T.pathCoverNumber ≤ 2) (D : Finset V) (dominates : T.IsTotalDominating D) :
    T.vertexCoverNum.toNat ≤ D.card := by
  classical
  obtain ⟨J,_,leJ,degJ,missing⟩ := linear_forest T tree hc
  let F := T.edgeFinset \ J.edgeFinset
  have ex : ∃ e ∈ T.edgeFinset, ∀ f∈F, f=e := by
    by_cases he : F.Nonempty
    · obtain ⟨e,he⟩ := he
      exact ⟨e,(mem_sdiff.mp he).1,fun f hf => card_le_one_iff.mp missing hf he⟩
    · have sz := tree.card_edgeFinset
      obtain ⟨e,he'⟩ := card_pos.mp (show 0 < T.edgeFinset.card by omega)
      exact ⟨e,he',fun f hf => (he ⟨f,hf⟩).elim⟩
  obtain ⟨e,he,all⟩ := ex
  induction e using Sym2.inductionOn with
  | _ x y =>
    have xy : T.Adj x y := mem_edgeFinset.mp he
    let U := T.deleteEdges {s(x,y)}
    have sub : U ≤ J := by
      intro v w h
      have hh := deleteEdges_adj.mp h
      by_contra! bad
      have hm : s(v,w) ∈ F := mem_sdiff.mpr ⟨mem_edgeFinset.mpr hh.1,fun h => bad (mem_edgeFinset.mp h)⟩
      exact hh.2 (Set.mem_singleton_iff.mpr (all _ hm))
    have crossdeg (v : V) : U.degree v ≤ 2 := (U.degree_le_of_le sub).trans (degJ v)
    have splitxy : ¬ U.Reachable x y := isBridge_iff.mp
      (isAcyclic_iff_forall_isBridge.mp tree.isAcyclic (mem_edgeFinset.mp he))
    obtain ⟨c⟩ := tree.colorable_two
    let red (v : V) : Prop := if U.Reachable x v then c v = c x else c v = c y
    let R := univ.filter red
    have isR (v : V) : v∈R ↔ red v := by simp [R]
    have xr : x ∈ R := (isR x).mpr (by simp [red])
    have yr : y ∈ R := (isR y).mpr (by simp [red,splitxy])
    have cross {v w : V} (h : U.Adj v w) : v ∈ R ↔ w ∉ R := by
      have top := (deleteEdges_adj.mp h).1
      have ne := c.valid top
      have eq : U.Reachable x v ↔ U.Reachable x w :=
        ⟨fun p => p.trans h.reachable,fun p => p.trans h.symm.reachable⟩
      rw [isR,isR]
      by_cases hv : U.Reachable x v
      · simp [red,hv,eq.mp hv]
        omega
      · have hw : ¬ U.Reachable x w := fun t => hv (eq.mpr t)
        simp only [red,if_neg hv,if_neg hw]
        omega
    have ua {v w : V} (h : T.Adj v w) : U.Adj v w ∨ (v=x ∧ w=y) ∨ (v=y ∧ w=x) := by
      by_cases eq : s(v,w) = s(x,y)
      · exact Or.inr (Sym2.eq_iff.mp eq)
      · exact Or.inl (deleteEdges_adj.mpr ⟨h,fun he => eq (Set.mem_singleton_iff.mp he)⟩)
    apply counting T tree D R dominates x y xy.ne xr yr
    · intro v vr w wr h
      rcases ua h with hj | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact vr ((cross hj).mpr wr)
      · exact vr xr
      · exact vr yr
    · intro v vr w wr h
      exact (ua h).resolve_left (fun hj => (cross hj).mp vr wr)
    · intro v vr
      have sub' : nbs T v Rᶜ ⊆ U.neighborFinset v := by
        intro w hw
        obtain ⟨ww,h⟩ := mem_filter.mp hw
        rcases ua h with hj | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact (mem_neighborFinset _ _ _).mpr hj
        · exact (mem_compl.mp ww yr).elim
        · exact (mem_compl.mp ww xr).elim
      exact (card_le_card sub').trans (crossdeg v)
    · intro v vr
      have sub' : nbs T v R ⊆ U.neighborFinset v := by
        intro w hw
        obtain ⟨_,h⟩ := mem_filter.mp hw
        rcases ua h with hj | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact (mem_neighborFinset _ _ _).mpr hj
        · exact (vr xr).elim
        · exact (vr yr).elim
      exact (card_le_card sub').trans (crossdeg v)

theorem two_paths (T : SimpleGraph V) (ht : T.IsTree) (hn : 2 ≤ Fintype.card V)
    (hc : T.pathCoverNumber ≤ 2) : T.vertexCoverNum.toNat ≤ T.totalDominationNumber := by
  classical
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  have ex : {k | ∃ D : Finset V, T.IsTotalNDominatingSet k D}.Nonempty := by
    refine ⟨univ.card,univ,⟨?_,rfl⟩⟩
    intro v
    obtain ⟨w,hw⟩ := exists_ne v
    obtain ⟨u,hu⟩ := (ht.connected v w).nonempty_neighborSet_left hw.symm
    exact ⟨u,mem_univ _,hu⟩
  obtain ⟨D,hD⟩ := Nat.sInf_mem ex
  rw [← show D.card = T.totalDominationNumber from hD.card_eq]
  exact join_parts T ht hn hc D hD.isTotalDominating
end OMA.TwoPaths

namespace OMA.TreeDomination
open SimpleGraph Finset
theorem bound {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V)
    (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    T.vertexCoverNum.toNat ≤ 2 * T.totalDominationNumber := by
  classical
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  have existsDom : {k | ∃ D : Finset V, T.IsTotalNDominatingSet k D}.Nonempty := by
    refine ⟨univ.card, univ, ⟨?_,rfl⟩⟩
    intro v
    obtain ⟨w,hw⟩ := exists_ne v
    obtain ⟨u,hu⟩ := (hT.connected v w).nonempty_neighborSet_left hw.symm
    exact ⟨u,mem_univ _,hu⟩
  obtain ⟨D,hD⟩ := Nat.sInf_mem existsDom
  have cardD : D.card = T.totalDominationNumber := hD.card_eq
  choose d hd ha using hD.isTotalDominating
  let edge (v : V) := s(v,d v)
  let used := Dᶜ.image edge
  let rest := T.edgeFinset \ used
  let cover := D ∪ rest.image (fun e => e.out.1)
  have subset : used ⊆ T.edgeFinset := by
    intro e he
    obtain ⟨v,_,rfl⟩ := mem_image.mp he
    exact mem_edgeFinset.mpr (ha v)
  have hinj : Set.InjOn edge (Dᶜ : Finset V) := by
    intro v hv w hw eq
    rcases Sym2.eq_iff.mp eq with e | e
    · exact e.1
    · have hnot : v ∉ D := mem_compl.mp hv
      exact (hnot (e.1 ▸ hd w)).elim
  have countUsed : used.card = Fintype.card V - D.card := by
    rw [show used.card = Dᶜ.card from card_image_of_injOn hinj,card_compl]
  have countRest : rest.card ≤ D.card := by
    have h := hT.card_edgeFinset
    have hdv := card_le_univ D
    have hn' : rest.card = T.edgeFinset.card - used.card := card_sdiff_of_subset subset
    omega
  have hcover : T.IsVertexCover cover := by
    intro v w h
    by_cases usedEdge : s(v,w) ∈ used
    · obtain ⟨u,_,hu⟩ := mem_image.mp usedEdge
      rcases Sym2.eq_iff.mp hu with e | e
      · exact Or.inr (mem_union_left _ (e.2 ▸ hd u))
      · exact Or.inl (mem_union_left _ (e.2 ▸ hd u))
    · have hm : s(v,w) ∈ rest := mem_sdiff.mpr ⟨mem_edgeFinset.mpr h,usedEdge⟩
      have hx : (s(v,w)).out.1 ∈ cover := mem_union_right _ (mem_image_of_mem _ hm)
      have he := (s(v,w)).out_fst_mem
      rcases Sym2.mem_iff.mp he with e | e
      · exact Or.inl (e ▸ hx)
      · exact Or.inr (e ▸ hx)
  have hc : T.vertexCoverNum.toNat ≤ cover.card := ENat.toNat_le_of_le_natCast (by
    simpa using hcover.vertexCoverNum_le)
  have hsize := card_union_le D (rest.image (fun e => e.out.1))
  have hrs := card_image_le (s := rest) (f := fun e => e.out.1)
  change cover.card ≤ _ at hsize
  omega
end OMA.TreeDomination

namespace OMA.TwoPaths

theorem regularized : type_of% @WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized := by
  intro V _ _ T ht hn
  by_cases hp : T.pathCoverNumber ≤ 2
  · rw [show max 1 (T.pathCoverNumber - 1) = 1 by omega, Nat.mul_one]
    exact two_paths T ht hn hp
  · have factor : 2 ≤ max 1 (T.pathCoverNumber - 1) := by omega
    calc
      _ ≤ 2 * T.totalDominationNumber := OMA.TreeDomination.bound T ht hn
      _ = T.totalDominationNumber * 2 := Nat.mul_comm _ _
      _ ≤ _ := Nat.mul_le_mul_left _ factor

end OMA.TwoPaths

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture372.conjecture372 := by
  intro V _ _ T ht hn hp
  have h := OMA.TwoPaths.regularized T ht (Nat.le_of_lt hn)
  have factor : max 1 (T.pathCoverNumber - 1) = T.pathCoverNumber - 1 := by omega
  rw [factor] at h
  have hr : (T.vertexCoverNum.toNat : ℝ) ≤
      (T.totalDominationNumber : ℝ) * ((T.pathCoverNumber - 1 : ℕ) : ℝ) := by exact_mod_cast h
  have hp' : 1 < (T.pathCoverNumber : ℝ) := by exact_mod_cast (show 1 < T.pathCoverNumber by omega)
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < T.pathCoverNumber - 1)).mpr
  simpa [Nat.cast_sub (by omega : 1 ≤ T.pathCoverNumber)] using hr
