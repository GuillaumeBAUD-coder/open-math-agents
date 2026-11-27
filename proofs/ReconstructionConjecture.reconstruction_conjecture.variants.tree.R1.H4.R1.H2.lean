import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric

-- Step ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1.H4.R1.H2
-- Credit: @jared-jasinski

namespace ReconTreeH4R1H2

open SimpleGraph

private lemma tree_path_length_eq_dist {U : Type} {T : SimpleGraph U} (hT : T.IsTree)
    {u v : U} {p : T.Walk u v} (hp : p.IsPath) : p.length = T.dist u v := by
  classical
  obtain ⟨q, hqlen⟩ := hT.connected.exists_walk_length_eq_dist u v
  have : Subsingleton (T.Path u v) :=
    (SimpleGraph.isAcyclic_iff_subsingleton_path.mp hT.isAcyclic) u v
  have heq : (⟨q.bypass, q.bypass_isPath⟩ : T.Path u v) = ⟨p, hp⟩ := Subsingleton.elim _ _
  have h1 : p.length ≤ q.length := by
    have hle := q.length_bypass_le_length
    have h2 : q.bypass = p := congrArg Subtype.val heq
    rwa [h2] at hle
  have h2 : T.dist u v ≤ p.length := T.dist_le p
  omega

-- For any edge a ~ b in a tree T, every vertex x has dist x b = dist x a + 1 (and b is not on
-- the path from x to a) OR dist x a = dist x b + 1 (and a is not on the path from x to b).
private lemma tree_edge_dichotomy {U : Type} {T : SimpleGraph U} (hT : T.IsTree)
    {a b : U} (hab : T.Adj a b) (x : U) :
    (T.dist x b = T.dist x a + 1 ∧
      ∀ (p : T.Walk x a), p.IsPath → b ∉ p.support) ∨
    (T.dist x a = T.dist x b + 1 ∧
      ∀ (p : T.Walk x b), p.IsPath → a ∉ p.support) := by
  classical
  obtain ⟨q0, -⟩ := hT.connected.exists_walk_length_eq_dist x a
  let q : T.Walk x a := q0.bypass
  have hq : q.IsPath := q0.bypass_isPath
  have hq_len : q.length = T.dist x a := tree_path_length_eq_dist hT hq
  by_cases hb : b ∈ q.support
  · right
    let q1 : T.Walk x b := q.takeUntil b hb
    let q2 : T.Walk b a := q.dropUntil b hb
    have hq1 : q1.IsPath := hq.takeUntil hb
    have hq2 : q2.IsPath := hq.dropUntil hb
    have hspec := congrArg Walk.length (q.take_spec hb)
    rw [Walk.length_append] at hspec
    change q1.length + q2.length = q.length at hspec
    let e : T.Walk b a := Walk.cons hab.symm Walk.nil
    have hq2_eq : q2 = e := by
      have he : e.IsPath := by
        rw [Walk.isPath_def]
        simp [e, (T.ne_of_adj hab).symm]
      have : Subsingleton (T.Path b a) :=
        (SimpleGraph.isAcyclic_iff_subsingleton_path.mp hT.isAcyclic) b a
      have heq : (⟨q2, hq2⟩ : T.Path b a) = ⟨e, he⟩ := Subsingleton.elim _ _
      exact congrArg Subtype.val heq
    have hq2_len : q2.length = 1 := by simp [hq2_eq, e]
    have hdist1 : T.dist x b = q1.length := (tree_path_length_eq_dist hT hq1).symm
    refine ⟨by omega, ?_⟩
    intro p hp ha_mem
    have : Subsingleton (T.Path x b) :=
      (SimpleGraph.isAcyclic_iff_subsingleton_path.mp hT.isAcyclic) x b
    have heq : (⟨p, hp⟩ : T.Path x b) = ⟨q1, hq1⟩ := Subsingleton.elim _ _
    have hp_eq : p = q1 := congrArg Subtype.val heq
    rw [hp_eq] at ha_mem
    -- a is the endpoint of q, so it cannot lie in q.takeUntil b (since b != a)
    have hq_supp := congrArg Walk.support (q.take_spec hb)
    rw [Walk.support_append] at hq_supp
    have ha_tail : a ∈ q2.support.tail := by
      rw [hq2_eq]
      simp [e]
    have hnodup := hq.support_nodup
    rw [← hq_supp, List.nodup_append] at hnodup
    exact hnodup.2.2 a ha_mem a ha_tail rfl
  · left
    let r : T.Walk x b := q.concat hab
    have hr : r.IsPath := by
      rw [Walk.isPath_def, Walk.support_concat, List.nodup_append]
      refine ⟨hq.support_nodup, List.nodup_singleton _, ?_⟩
      intro z hz y hy
      simp only [List.mem_singleton] at hy
      subst hy
      exact fun h => hb (h ▸ hz)
    have hr_len : r.length = T.dist x b := tree_path_length_eq_dist hT hr
    have hr_len' : r.length = q.length + 1 := Walk.length_concat q hab
    refine ⟨by omega, ?_⟩
    intro p hp hb_mem
    have : Subsingleton (T.Path x a) :=
      (SimpleGraph.isAcyclic_iff_subsingleton_path.mp hT.isAcyclic) x a
    have heq : (⟨p, hp⟩ : T.Path x a) = ⟨q, hq⟩ := Subsingleton.elim _ _
    have hp_eq : p = q := congrArg Subtype.val heq
    exact hb (hp_eq ▸ hb_mem)

-- If dist x a < dist x b, then every vertex z on the unique path from x to a also has dist z a < dist z b.
private lemma side_closed_along_path {U : Type} {T : SimpleGraph U} (hT : T.IsTree)
    {a b x : U} (hab : T.Adj a b) (hside : T.dist x a < T.dist x b)
    {p : T.Walk x a} (hp : p.IsPath) {z : U} (hz : z ∈ p.support) :
    T.dist z a < T.dist z b := by
  classical
  have hb_not : b ∉ p.support := by
    rcases tree_edge_dichotomy hT hab x with ⟨_, h⟩ | ⟨h, _⟩
    · exact h p hp
    · omega
  let pz : T.Walk z a := p.dropUntil z hz
  have hpz : pz.IsPath := hp.dropUntil hz
  have hb_not_z : b ∉ pz.support := fun hmem =>
    hb_not (Walk.support_dropUntil_subset_support p hz hmem)
  let rz : T.Walk z b := pz.concat hab
  have hrz : rz.IsPath := by
    rw [Walk.isPath_def, Walk.support_concat, List.nodup_append]
    refine ⟨hpz.support_nodup, List.nodup_singleton _, ?_⟩
    intro w hw y hy
    simp only [List.mem_singleton] at hy
    subst hy
    exact fun h => hb_not_z (h ▸ hw)
  have h1 := tree_path_length_eq_dist hT hpz
  have h2 := tree_path_length_eq_dist hT hrz
  have h3 : rz.length = pz.length + 1 := Walk.length_concat pz hab
  omega

-- Lifting a walk whose support stays in S into T.induce S.
private lemma walk_lift_induce {U : Type} {T : SimpleGraph U} {S : Set U}
    {u v : U} (p : T.Walk u v) (hp : ∀ w ∈ p.support, w ∈ S) :
    (T.induce S).Reachable ⟨u, hp u p.start_mem_support⟩ ⟨v, hp v p.end_mem_support⟩ := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons a b c hab rest ih =>
    have ha : a ∈ S := hp a (by simp)
    have hrest : ∀ w ∈ rest.support, w ∈ S := fun w hw => hp w (by simp [hw])
    have hb : b ∈ S := hrest b rest.start_mem_support
    have hadj : (T.induce S).Adj ⟨a, ha⟩ ⟨b, hb⟩ := hab
    exact (Adj.reachable hadj).trans (ih hrest)

-- Any induced subgraph of an acyclic graph is acyclic.
private lemma isAcyclic_induce {U : Type} {T : SimpleGraph U} (hA : T.IsAcyclic) (S : Set U) :
    (T.induce S).IsAcyclic := by
  intro v c hc
  let f : T.induce S ↪g T := Embedding.induce S
  exact hA (c.map f.toHom) (Walk.IsCycle.map f.injective hc)

-- The side {x | dist x a < dist x b} induces a tree.
private lemma side_isTree {U : Type} {T : SimpleGraph U} (hT : T.IsTree)
    {a b : U} (hab : T.Adj a b) :
    (T.induce {x : U | T.dist x a < T.dist x b}).IsTree := by
  classical
  have ha_mem : a ∈ {x : U | T.dist x a < T.dist x b} := by
    change T.dist a a < T.dist a b
    rw [T.dist_self]
    have hne : T.dist a b ≠ 0 := fun h0 => T.ne_of_adj hab ((hT.connected.dist_eq_zero_iff).mp h0)
    omega
  have : Nonempty {x : U | T.dist x a < T.dist x b} := ⟨⟨a, ha_mem⟩⟩
  refine ⟨⟨?_⟩, isAcyclic_induce hT.isAcyclic _⟩
  intro ⟨x, hx⟩ ⟨y, hy⟩
  have reach_a : ∀ (w : U) (hw : w ∈ {x : U | T.dist x a < T.dist x b}),
      (T.induce {x : U | T.dist x a < T.dist x b}).Reachable ⟨w, hw⟩ ⟨a, ha_mem⟩ := by
    intro w hw
    obtain ⟨q0, -⟩ := hT.connected.exists_walk_length_eq_dist w a
    let q := q0.bypass
    have hq : q.IsPath := q0.bypass_isPath
    have hsupp : ∀ z ∈ q.support, z ∈ {x : U | T.dist x a < T.dist x b} := fun z hz =>
      side_closed_along_path hT hab hw hq hz
    exact walk_lift_induce q hsupp
  exact (reach_a x hx).trans (reach_a y hy).symm

-- Distance factorization across an edge a ~ b in a tree.
private lemma dist_across_edge {U : Type} {T : SimpleGraph U} (hT : T.IsTree)
    {a b x y : U} (hab : T.Adj a b)
    (hx : T.dist x a < T.dist x b) (hy : T.dist y b < T.dist y a) :
    T.dist x y = T.dist x a + 1 + T.dist b y := by
  classical
  obtain ⟨p0, -⟩ := hT.connected.exists_walk_length_eq_dist x a
  obtain ⟨q0, -⟩ := hT.connected.exists_walk_length_eq_dist b y
  let p := p0.bypass
  let q := q0.bypass
  have hp : p.IsPath := p0.bypass_isPath
  have hq : q.IsPath := q0.bypass_isPath
  have hdisj : ∀ z ∈ p.support, z ∉ q.support := by
    intro z hzp hzq
    have h1 : T.dist z a < T.dist z b := side_closed_along_path hT hab hx hp hzp
    have h2 : T.dist z b < T.dist z a :=
      side_closed_along_path hT hab.symm hy hq.reverse (by simpa [Walk.support_reverse] using hzq)
    omega
  let w : T.Walk x y := p.append (Walk.cons hab q)
  have hw : w.IsPath := by
    rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons, List.nodup_append]
    refine ⟨hp.support_nodup, hq.support_nodup, ?_⟩
    intro z hzp u huq hzu
    exact hdisj z hzp (hzu ▸ huq)
  have hw_len : w.length = T.dist x y := tree_path_length_eq_dist hT hw
  have hp_len : p.length = T.dist x a := tree_path_length_eq_dist hT hp
  have hq_len : q.length = T.dist b y := tree_path_length_eq_dist hT hq
  have hlen : w.length = p.length + 1 + q.length := by
    simp [w, Walk.length_append, Walk.length_cons]
    omega
  omega

end ReconTreeH4R1H2

open SimpleGraph in
theorem OMA.solution : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1.H2 := by
  classical
  intro U _ T hT hd3 hodd
  obtain ⟨r, hr⟩ := hodd
  have hr_pos : 1 ≤ r := by omega
  have hdiv : (T.diam - 1) / 2 = r := by omega
  have : Nonempty U := by
    have hne : T.diam ≠ 0 := by omega
    exact ⟨(T.nontrivial_of_diam_ne_zero hne).exists_pair_ne.choose⟩
  obtain ⟨u, v, huv⟩ := T.exists_dist_eq_diam
  obtain ⟨p0, -⟩ := hT.connected.exists_walk_length_eq_dist u v
  let p : T.Walk u v := p0.bypass
  have hp : p.IsPath := p0.bypass_isPath
  have hp_len : p.length = 2 * r + 1 := by
    rw [ReconTreeH4R1H2.tree_path_length_eq_dist hT hp, huv, hr]
  let c₁ : U := p.getVert r
  let c₂ : U := p.getVert (r + 1)
  have hadj : T.Adj c₁ c₂ := p.adj_getVert_succ (by omega : r < p.length)
  have hc₁_mem : c₁ ∈ p.support := p.getVert_mem_support r
  have hc₂_mem : c₂ ∈ p.support := p.getVert_mem_support (r + 1)
  have hidx1 : p.support.idxOf c₁ = r := by
    dsimp only [c₁]
    rw [Walk.getVert_eq_support_getElem p (by omega)]
    exact hp.support_nodup.idxOf_getElem r (by rw [Walk.length_support]; omega)
  have hidx2 : p.support.idxOf c₂ = r + 1 := by
    dsimp only [c₂]
    rw [Walk.getVert_eq_support_getElem p (by omega)]
    exact hp.support_nodup.idxOf_getElem (r + 1) (by rw [Walk.length_support]; omega)
  have hdist_uc1 : T.dist u c₁ = r := by
    rw [← ReconTreeH4R1H2.tree_path_length_eq_dist hT (hp.takeUntil hc₁_mem),
      Walk.length_takeUntil, hidx1]
  have hdist_uc2 : T.dist u c₂ = r + 1 := by
    rw [← ReconTreeH4R1H2.tree_path_length_eq_dist hT (hp.takeUntil hc₂_mem),
      Walk.length_takeUntil, hidx2]
  have hdist_c1v : T.dist c₁ v = r + 1 := by
    have hspec := congrArg Walk.length (p.take_spec hc₁_mem)
    rw [Walk.length_append, Walk.length_takeUntil, hidx1] at hspec
    rw [← ReconTreeH4R1H2.tree_path_length_eq_dist hT (hp.dropUntil hc₁_mem)]
    omega
  have hdist_c2v : T.dist c₂ v = r := by
    have hspec := congrArg Walk.length (p.take_spec hc₂_mem)
    rw [Walk.length_append, Walk.length_takeUntil, hidx2] at hspec
    rw [← ReconTreeH4R1H2.tree_path_length_eq_dist hT (hp.dropUntil hc₂_mem)]
    omega
  have hdist_vc1 : T.dist v c₁ = r + 1 := by rw [T.dist_comm, hdist_c1v]
  have hdist_vc2 : T.dist v c₂ = r := by rw [T.dist_comm, hdist_c2v]
  have hne_dist : ∀ x : U, T.dist x c₁ ≠ T.dist x c₂ := by
    intro x
    rcases ReconTreeH4R1H2.tree_edge_dichotomy hT hadj x with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hfact : ∀ x y : U, T.dist x c₁ < T.dist x c₂ → T.dist y c₂ < T.dist y c₁ →
      T.dist x y = T.dist x c₁ + 1 + T.dist c₂ y := by
    intro x y hx hy
    exact ReconTreeH4R1H2.dist_across_edge hT hadj hx hy
  have hediam : T.ediam ≠ ⊤ := T.connected_iff_ediam_ne_top.mp hT.connected
  have edist_eq : ∀ a b : U, T.edist a b = (T.dist a b : ℕ∞) := fun a b =>
    (ENat.natCast_toNat (ne_top_of_le_ne_top hediam T.edist_le_ediam)).symm
  have hbound1 : ∀ x : U, T.dist x c₁ < T.dist x c₂ → T.dist x c₁ ≤ r := by
    intro x hx
    have hxv := hfact x v hx (by omega)
    have hle : T.dist x v ≤ 2 * r + 1 := hr ▸ T.dist_le_diam hediam
    omega
  have hbound2 : ∀ x : U, T.dist x c₂ < T.dist x c₁ → T.dist x c₂ ≤ r := by
    intro x hx
    have hux := hfact u x (by omega) hx
    have hle : T.dist u x ≤ 2 * r + 1 := hr ▸ T.dist_le_diam hediam
    have hcomm : T.dist c₂ x = T.dist x c₂ := T.dist_comm
    omega
  have hecc_c1 : T.eccent c₁ = ((r + 1 : ℕ) : ℕ∞) := by
    apply le_antisymm
    · rw [T.eccent_le_iff]
      intro x
      rw [edist_eq c₁ x, T.dist_comm]
      rcases ReconTreeH4R1H2.tree_edge_dichotomy hT hadj x with ⟨h, _⟩ | ⟨h, _⟩
      · have := hbound1 x (by omega)
        exact_mod_cast (by omega : T.dist x c₁ ≤ r + 1)
      · have := hbound2 x (by omega)
        exact_mod_cast (by omega : T.dist x c₁ ≤ r + 1)
    · have hle : T.edist c₁ v ≤ T.eccent c₁ := T.edist_le_eccent
      rw [edist_eq c₁ v, hdist_c1v] at hle
      exact hle
  have hecc_c2 : T.eccent c₂ = ((r + 1 : ℕ) : ℕ∞) := by
    apply le_antisymm
    · rw [T.eccent_le_iff]
      intro x
      rw [edist_eq c₂ x, T.dist_comm]
      rcases ReconTreeH4R1H2.tree_edge_dichotomy hT hadj x with ⟨h, _⟩ | ⟨h, _⟩
      · have := hbound1 x (by omega)
        exact_mod_cast (by omega : T.dist x c₂ ≤ r + 1)
      · have := hbound2 x (by omega)
        exact_mod_cast (by omega : T.dist x c₂ ≤ r + 1)
    · have hle : T.edist c₂ u ≤ T.eccent c₂ := T.edist_le_eccent
      rw [edist_eq c₂ u, T.dist_comm, hdist_uc2] at hle
      exact hle
  have hecc_gt : ∀ x : U, x ≠ c₁ → x ≠ c₂ → ((r + 1 : ℕ) : ℕ∞) < T.eccent x := by
    intro x hx1 hx2
    rcases ReconTreeH4R1H2.tree_edge_dichotomy hT hadj x with ⟨h, _⟩ | ⟨h, _⟩
    · have hpos : 0 < T.dist x c₁ := by
        have h0 : T.dist x c₁ ≠ 0 := fun h0 => hx1 ((hT.connected.dist_eq_zero_iff).mp h0)
        omega
      have hxv := hfact x v (by omega) (by omega)
      have hlt : ((r + 1 : ℕ) : ℕ∞) < T.edist x v := by
        rw [edist_eq x v]
        exact_mod_cast (by omega : r + 1 < T.dist x v)
      exact lt_of_lt_of_le hlt T.edist_le_eccent
    · have hpos : 0 < T.dist x c₂ := by
        have h0 : T.dist x c₂ ≠ 0 := fun h0 => hx2 ((hT.connected.dist_eq_zero_iff).mp h0)
        omega
      have hux := hfact u x (by omega) (by omega)
      have hcomm1 : T.dist c₂ x = T.dist x c₂ := T.dist_comm
      have hcomm2 : T.dist u x = T.dist x u := T.dist_comm
      have hlt : ((r + 1 : ℕ) : ℕ∞) < T.edist x u := by
        rw [edist_eq x u]
        exact_mod_cast (by omega : r + 1 < T.dist x u)
      exact lt_of_lt_of_le hlt T.edist_le_eccent
  have hrad : T.radius = ((r + 1 : ℕ) : ℕ∞) := by
    apply le_antisymm
    · exact hecc_c1 ▸ T.radius_le_eccent
    · obtain ⟨w, hw⟩ := T.exists_eccent_eq_radius
      rw [← hw]
      by_cases h1 : w = c₁
      · rw [h1, hecc_c1]
      · by_cases h2 : w = c₂
        · rw [h2, hecc_c2]
        · exact (hecc_gt w h1 h2).le
  have hcenter : T.center = {c₁, c₂} := by
    ext x
    rw [T.mem_center_iff, hrad, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hnot
      push Not at hnot
      exact (ne_of_gt (hecc_gt x hnot.1 hnot.2)) hx
    · rintro (rfl | rfl)
      · exact hecc_c1
      · exact hecc_c2
  refine ⟨c₁, c₂, hadj, hcenter, hne_dist, ?_, ?_,
    ReconTreeH4R1H2.side_isTree hT hadj,
    ReconTreeH4R1H2.side_isTree hT hadj.symm, hfact⟩
  · intro x hx; rw [hdiv]; exact hbound1 x hx
  · intro x hx; rw [hdiv]; exact hbound2 x hx
