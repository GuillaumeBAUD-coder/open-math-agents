import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1
/-! The central edge of an odd-diameter tree separates two rooted subtrees. -/
namespace TreeDiam
open SimpleGraph
lemma path_dist {V : Type} {G : SimpleGraph V} (hG : G.IsTree)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) : p.length = G.dist u v := by
  obtain ⟨q, hq⟩ := hG.connected.exists_walk_length_eq_dist u v
  have he := (hG.isAcyclic.subsingleton_path u v).elim (⟨p,hp⟩ : G.Path u v) ⟨q,q.isPath_of_length_eq_dist hq⟩
  exact (congrArg (fun w : G.Path u v => w.1.length) he).trans hq


lemma split_dist {V : Type} {G : SimpleGraph V} (ht : G.IsTree)
    {u v c : V} {p : G.Walk u v} (hp : p.IsPath) (hc : c ∈ p.support) :
    G.dist u v = G.dist u c + G.dist c v := by
  classical
  have h := congrArg Walk.length (p.take_spec hc)
  rw [Walk.length_append, path_dist ht (hp.takeUntil hc), path_dist ht (hp.dropUntil hc), path_dist ht hp] at h
  exact h.symm

lemma split_side {V : Type} {G : SimpleGraph V} (ht : G.IsTree)
    {a b c : V} {p : G.Walk a b} (hp : p.IsPath) (hc : c ∈ p.support) (x : V) :
    G.dist a x = G.dist a c + G.dist c x ∨ G.dist x b = G.dist x c + G.dist c b := by
  classical
  obtain ⟨q,hq,_⟩ := ht.existsUnique_path a x
  obtain ⟨s,hs,_⟩ := ht.existsUnique_path x b
  let w := q.append s
  have he := (ht.isAcyclic.subsingleton_path a b).elim (⟨p,hp⟩ : G.Path a b) w.toPath
  have hw : c ∈ w.support := w.support_toPath_subset_support (he ▸ hc)
  rcases (Walk.mem_support_append_iff q s).mp hw with h | h
  · exact Or.inl (split_dist ht hq h)
  · exact Or.inr (split_dist ht hs h)


lemma cross_edge {V : Type} {G : SimpleGraph V} (ht : G.IsTree) {c d : V}
    (hcd : G.Adj c d) {x y : V} (hx : G.dist x c < G.dist x d)
    (hy : G.dist y d < G.dist y c) :
    G.dist x y = G.dist x c + 1 + G.dist d y := by
  classical
  obtain ⟨p,hp,_⟩ := ht.existsUnique_path x c
  have hd : d ∉ p.support := by
    intro hd
    have := split_dist ht hp hd
    omega
  have hc := p.support_subset_support_concat hcd p.end_mem_support
  have hs := split_side ht (hp.concat hd hcd) hc y
  have step := ht.dist_eq_dist_add_one_of_adj y hcd
  have co := G.dist_comm (u := c) (v := y)
  have do' := G.dist_comm (u := d) (v := y)
  omega

lemma side_tree {V : Type} {G : SimpleGraph V} (ht : G.IsTree) {c d : V} (hcd : G.Adj c d) :
    (G.induce {x | G.dist x c < G.dist x d}).IsTree := by
  classical
  let S := {x | G.dist x c < G.dist x d}
  have hc : c ∈ S := by simp [S, dist_eq_one_iff_adj.2 hcd]
  refine ⟨(?_ : (G.induce S).Connected), ht.isAcyclic.induce _⟩
  apply (G.induce S).connected_iff_exists_forall_reachable.2
  refine ⟨⟨c,hc⟩, ?_⟩
  intro x
  obtain ⟨p,hp,_⟩ := ht.existsUnique_path (x : V) c
  have hsup (y : V) (hy : y ∈ p.support) : y ∈ S := by
    have hsplit := split_dist ht hp hy
    have htr := ht.connected.dist_triangle (u := (x : V)) (v := y) (w := d)
    have hx : G.dist x c < G.dist x d := x.property
    change G.dist y c < G.dist y d
    omega
  exact ⟨(p.induce S hsup).reverse⟩

theorem odd_edge {V : Type} [Fintype V] (G : SimpleGraph V) (ht : G.IsTree)
    (hthree : 3 ≤ G.diam) (ho : Odd G.diam) :
    ∃ c d : V, G.Adj c d ∧ G.center = {c,d} ∧
      (∀ x, G.dist x c ≠ G.dist x d) ∧
      (∀ x, G.dist x c < G.dist x d → G.dist x c ≤ (G.diam-1)/2) ∧
      (∀ x, G.dist x d < G.dist x c → G.dist x d ≤ (G.diam-1)/2) ∧
      (G.induce {x | G.dist x c < G.dist x d}).IsTree ∧
      (G.induce {x | G.dist x d < G.dist x c}).IsTree ∧
      ∀ x y, G.dist x c < G.dist x d → G.dist y d < G.dist y c →
        G.dist x y = G.dist x c + 1 + G.dist d y := by
  have := ht.connected.nonempty
  obtain ⟨r,hr⟩ := ho
  obtain ⟨a,b,hab⟩ := G.exists_dist_eq_diam
  obtain ⟨p,hp,_⟩ := ht.existsUnique_path a b
  have hl : p.length = 2*r+1 := (path_dist ht hp).trans (hab.trans hr)
  let c := p.getVert r
  let d := p.getVert (r+1)
  have hcd : G.Adj c d := p.adj_getVert_succ (by omega)
  have left (i : ℕ) (hi : i ≤ p.length) : G.dist a (p.getVert i) = i := by
    rw [← path_dist ht (hp.take i), Walk.take_length, min_eq_left hi]
  have right (i : ℕ) : G.dist (p.getVert i) b = p.length - i := by
    rw [← path_dist ht (hp.drop i), Walk.drop_length]
  have ac : G.dist a c = r := left _ (by omega)
  have ad : G.dist a d = r+1 := left _ (by omega)
  have cb : G.dist c b = r+1 := by change G.dist (p.getVert r) b = _; rw [right]; omega
  have db : G.dist d b = r := by change G.dist (p.getVert (r+1)) b = _; rw [right]; omega
  have bd : G.dist b d = r := G.dist_comm.trans db
  have bc : G.dist b c = r+1 := G.dist_comm.trans cb
  have al : G.dist a c < G.dist a d := by omega
  have br : G.dist b d < G.dist b c := by omega
  have bound (v w : V) : G.dist v w ≤ G.diam := G.dist_le_diam (G.connected_iff_ediam_ne_top.mp ht.connected)
  have lo (x : V) (hx : G.dist x c < G.dist x d) : G.dist x c ≤ r := by
    have := cross_edge ht hcd hx br
    have := bound x b
    omega
  have ro (x : V) (hx : G.dist x d < G.dist x c) : G.dist x d ≤ r := by
    have := cross_edge ht hcd al hx
    have := bound a x
    have := G.dist_comm (u := d) (v := x)
    omega
  have ne (x : V) : G.dist x c ≠ G.dist x d := ht.dist_ne_of_adj x hcd
  have eb (v w : V) : (G.dist v w : ℕ∞) ≤ G.eccent v :=
    (ht.connected v w).coe_dist_eq_edist.trans_le G.edist_le_eccent
  have high (v : V) : (↑(r+1) : ℕ∞) ≤ G.eccent v := by
    rcases (ne v).lt_or_gt with h | h
    · have := cross_edge ht hcd h br
      exact le_trans (by exact_mod_cast (show r+1 ≤ G.dist v b by omega)) (eb v b)
    · have := cross_edge ht hcd al h
      have := G.dist_comm (u := a) (v := v)
      exact le_trans (by exact_mod_cast (show r+1 ≤ G.dist v a by omega)) (eb v a)
  have both (v : V) : G.dist v c ≤ r+1 ∧ G.dist v d ≤ r+1 := by
    have step := ht.dist_eq_dist_add_one_of_adj v hcd
    rcases (ne v).lt_or_gt with h | h
    · have := lo v h
      omega
    · have := ro v h
      omega
  have cen (v : V) (h : ∀ x, G.dist x v ≤ r+1) : G.eccent v = ↑(r+1) := by
    apply le_antisymm _ (high v)
    apply (G.eccent_le_iff _ _).2
    intro x
    rw [G.edist_comm, ← (ht.connected x v).coe_dist_eq_edist]
    exact_mod_cast h x
  have ce := cen c (fun x => (both x).1)
  have de := cen d (fun x => (both x).2)
  have rad : G.radius = ↑(r+1) :=
    le_antisymm (ce ▸ G.radius_le_eccent (u := c)) (le_iInf high)
  have unique (x : V) (hc : x ≠ c) (hd : x ≠ d) : (↑(r+1) : ℕ∞) < G.eccent x := by
    rcases (ne x).lt_or_gt with h | h
    · have := ht.connected.pos_dist_of_ne hc
      have := cross_edge ht hcd h br
      exact lt_of_lt_of_le (by exact_mod_cast (show r+1 < G.dist x b by omega)) (eb x b)
    · have := ht.connected.pos_dist_of_ne hd
      have := cross_edge ht hcd al h
      have := G.dist_comm (u := a) (v := x)
      have := G.dist_comm (u := d) (v := x)
      exact lt_of_lt_of_le (by exact_mod_cast (show r+1 < G.dist x a by omega)) (eb x a)
  have eqcenter : G.center = {c,d} := by
    ext x
    rw [G.mem_center_iff, rad]
    change _ ↔ x = c ∨ x = d
    constructor
    · intro he
      by_contra! h
      exact (unique x h.1 h.2).ne' he
    · rintro (rfl | rfl)
      · exact ce
      · exact de
  have hr' : (G.diam-1)/2 = r := by omega
  exact ⟨c,d,hcd,eqcenter,ne,hr' ▸ lo,hr' ▸ ro,side_tree ht hcd,side_tree ht hcd.symm,
    fun _ _ hx hy => cross_edge ht hcd hx hy⟩
end TreeDiam

theorem OMA.solution : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1.H2 := by
  intro V _ G ht hmin ho
  exact TreeDiam.odd_edge G ht hmin ho
