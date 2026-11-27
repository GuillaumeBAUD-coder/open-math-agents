import FormalConjectures.ErdosProblems.«713»
import Mathlib.Analysis.Subadditive
import Mathlib.Logic.Equiv.Fintype

/-!
Reduce the bipartite Turán asymptotic question to connected cyclic graphs of
diverging edge count per vertex and disconnected graphs of at most linear
growth. For a connected forbidden graph, extremal numbers are superadditive by
disjoint union of hosts. Fekete's lemma gives a positive linear limit unless
the ratios diverge. A minimum-degree argument proves a linear bound for every
forest. Isolated vertices can be removed without changing eventual values.

For a disjoint union of forbidden graphs, the greater of the two component
extremal numbers approximates the full extremal number up to an additive O(n)
term: first embed one component, then avoid its occupied vertices when placing
the other. Superlinear leading powers and coefficients therefore pass through
finite disjoint unions. For a forbidden matching with k edges the leading term
is (k-1)n: coloring host edges by endpoint sum modulo n gives the upper bound,
and a complete bipartite host gives the lower bound. Induction leaves the two
classes below.

The question originates in Erdős and Simonovits, Some extremal problems in
graph theory, Combinatorial Theory and its Applications (1970), 377–390.
-/

-- Credit: @zarnab222-dev

section

open SimpleGraph Finset

namespace E713Super

theorem free_sum {W X Y : Type*} {G : SimpleGraph W} {A : SimpleGraph X} {B : SimpleGraph Y}
    (connected : G.Connected) (freeA : G.Free A) (freeB : G.Free B) : G.Free (A ⊕g B) := by
  classical
  rintro ⟨f⟩
  obtain ⟨root⟩ := connected.nonempty
  have reach (w : W) := connected root w
  cases hroot : f root with
  | inl a =>
    have inLeft (w : W) : ∃ x : X, f w = Sum.inl x := by
      cases hw : f w with
      | inl x => exact ⟨x,rfl⟩
      | inr y =>
        have path := (reach w).map f.toHom
        change (A ⊕g B).Reachable (f root) (f w) at path
        rw [hroot,hw] at path
        exact (not_reachable_sum_inl_inr a y path).elim
    choose g hg using inLeft
    let hom : G →g A := ⟨g, fun {x y} h => by
      have adj := f.toHom.map_rel' h
      change (A ⊕g B).Adj (f x) (f y) at adj
      rw [hg,hg] at adj
      exact sum_adj_inl.mp adj⟩
    apply freeA
    refine ⟨hom.toCopy ?_⟩
    intro x y h
    apply f.injective
    change f x = f y
    rw [hg x,hg y]
    exact congrArg Sum.inl h
  | inr b =>
    have inRight (w : W) : ∃ y : Y, f w = Sum.inr y := by
      cases hw : f w with
      | inr y => exact ⟨y,rfl⟩
      | inl x =>
        have path := (reach w).map f.toHom
        change (A ⊕g B).Reachable (f root) (f w) at path
        rw [hroot,hw] at path
        exact (not_reachable_sum_inl_inr x b path.symm).elim
    choose g hg using inRight
    let hom : G →g B := ⟨g, fun {x y} h => by
      have adj := f.toHom.map_rel' h
      change (A ⊕g B).Adj (f x) (f y) at adj
      rw [hg,hg] at adj
      exact sum_adj_inr.mp adj⟩
    apply freeB
    refine ⟨hom.toCopy ?_⟩
    intro x y h
    apply f.injective
    change f x = f y
    rw [hg x,hg y]
    exact congrArg Sum.inr h

theorem superadditive_of_ne_bot {W : Type*} (G : SimpleGraph W)
    (connected : G.Connected) (hG : G ≠ ⊥) (m n : ℕ) :
    extremalNumber m G + extremalNumber n G ≤ extremalNumber (m+n) G := by
  classical
  obtain ⟨A,dA,hA⟩ := exists_isExtremal_free (V := Fin m) hG
  obtain ⟨B,dB,hB⟩ := exists_isExtremal_free (V := Fin n) hG
  let _ : DecidableRel A.Adj := dA
  let _ : DecidableRel B.Adj := dB
  have aedges : A.edgeFinset.card = extremalNumber m G := by
    simpa using card_edgeFinset_of_isExtremal_free hA
  have bedges : B.edgeFinset.card = extremalNumber n G := by
    simpa using card_edgeFinset_of_isExtremal_free hB
  have sumedges : (A ⊕g B).edgeFinset.card = A.edgeFinset.card + B.edgeFinset.card := by
    simp only [edgeFinset_card]
    simpa only [Fintype.card_sum] using Fintype.card_congr (edgeSetSumEquiv (G:=A) (H:=B))
  have hf := free_sum connected hA.prop hB.prop
  have h := card_edgeFinset_le_extremalNumber hf
  simpa only [Fintype.card_sum, Fintype.card_fin, sumedges, aedges, bedges] using h

theorem superadditive {W : Type*} [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (connected : G.Connected) (edges : 2 ≤ G.edgeFinset.card) (m n : ℕ) :
    extremalNumber m G + extremalNumber n G ≤ extremalNumber (m+n) G := by
  apply superadditive_of_ne_bot G connected _ m n
  intro h
  rw [edgeFinset_eq_empty.mpr h] at edges
  simp at edges

theorem positive_at_two {W : Type*} [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (edges : 2 ≤ G.edgeFinset.card) : 0 < extremalNumber 2 G := by
  classical
  let K : SimpleGraph (Fin 2) := ⊤
  have cardK : K.edgeFinset.card = 1 := by
    dsimp only [K]
    rw [card_edgeFinset_top_eq_card_choose_two]
    decide
  have hf : G.Free K := by
    rintro ⟨f⟩
    have h := Fintype.card_le_of_embedding f.mapEdgeSet
    rw [← G.edgeFinset_card, ← K.edgeFinset_card,cardK] at h
    omega
  have h := card_edgeFinset_le_extremalNumber hf
  have h' : 1 ≤ extremalNumber 2 G := by simpa [cardK] using h
  omega

end E713Super

end

section

open Filter Asymptotics Set
open scoped Topology

namespace E713Fekete

private theorem density_alternative (a : ℕ → ℕ)
    (add : ∀ m n, a m + a n ≤ a (m+n)) (positive : 0 < a 2) :
    (∃ c : ℝ, 0 < c ∧ IsEquivalent atTop (fun n : ℕ => (a n : ℝ)) (fun n => c * n)) ∨
      Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop atTop := by
  let u (n : ℕ) : ℝ := -(a n : ℝ)
  have sub : Subadditive u := by
    intro m n
    have le : (a m : ℝ) + a n ≤ a (m+n) := by exact_mod_cast add m n
    dsimp [u]
    linarith
  by_cases bounded : BddBelow (range fun n : ℕ => u n / n)
  · left
    have lim := sub.tendsto_lim bounded
    have atTwo := sub.lim_le_div bounded (by decide : 2 ≠ (0 : ℕ))
    have pos : 0 < -sub.lim := by
      have pos' : (0 : ℝ) < a 2 := by exact_mod_cast positive
      norm_num [u] at atTwo
      linarith
    refine ⟨-sub.lim,pos,isEquivalent_of_tendsto_one ?_⟩
    have t : Tendsto (fun n : ℕ => (a n : ℝ)/n / (-sub.lim)) atTop (𝓝 1) := by
      have := lim.neg.div_const (-sub.lim)
      simpa only [u,neg_div,neg_neg,div_self pos.ne'] using this
    apply t.congr'
    filter_upwards with n
    show (a n : ℝ) / n / (-sub.lim) = (a n : ℝ) / ((-sub.lim) * n)
    rw [div_div,mul_comm]
  · right
    apply tendsto_atTop.mpr
    intro M
    obtain ⟨k,hk,small⟩ : ∃ k : ℕ, k ≠ 0 ∧ u k / k < -(|M|+1) := by
      by_contra! h
      apply bounded
      refine ⟨-(|M|+1), ?_⟩
      rintro x ⟨k,rfl⟩
      rcases eq_or_ne k 0 with rfl | hn
      · simp only [Nat.cast_zero,div_zero]
        linarith [abs_nonneg M]
      · exact h k hn
    filter_upwards [sub.eventually_div_lt_of_div_lt hk small] with n low
    dsimp [u] at low
    rw [neg_div] at low
    linarith [le_abs_self M]

end E713Fekete

end

section

open Finset SimpleGraph

namespace E713Core

private theorem degree_irrel {W : Type*} (G : SimpleGraph W) (w : W)
    (a b : Fintype (G.neighborSet w)) :
    @SimpleGraph.degree W G w a = @SimpleGraph.degree W G w b := by
  cases Subsingleton.elim a b
  rfl

theorem dense_core {V : Type*} [Fintype V] [DecidableEq V]
    (X : SimpleGraph V) [DecidableRel X.Adj] (q : ℕ)
    (large : q * Fintype.card V < X.edgeFinset.card) :
    ∃ (U : Finset V) (_ : (U : Set V)),
      ∀ x : (U : Set V), q ≤ (X.induce (U : Set V)).degree x := by
  classical
  let edges (U : Finset V) := X.edgeFinset ∩ U.sym2
  have start : ∃ k, ∃ U : Finset V, U.card = k ∧ q*U.card < (edges U).card := by
    refine ⟨_,univ,rfl,?_⟩
    simpa [edges] using large
  obtain ⟨U,hU,dense⟩ := Nat.find_spec start
  have nonempty : U.Nonempty := by
    by_contra! h
    simp [h,edges] at dense
  obtain ⟨u,hu⟩ := nonempty
  refine ⟨U,⟨u,hu⟩,?_⟩
  intro x
  let inside := X.neighborFinset x.val ∩ U
  have deg : (X.induce (U : Set V)).degree x = inside.card := by
    have mapEq := SimpleGraph.map_neighborFinset_induce (G := X) (s := (U : Set V)) x
    have count := congrArg Finset.card mapEq
    rw [card_map,card_neighborFinset_eq_degree,Finset.toFinset_coe] at count
    exact (degree_irrel _ _ _ _).trans count
  have cover : edges U ⊆ edges (U.erase x.val) ∪ inside.image (fun y => s(x.val,y)) := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      obtain ⟨hab,hends⟩ := mem_inter.mp he
      obtain ⟨ha,hb⟩ := mk_mem_sym2_iff.mp hends
      have adj : X.Adj a b := X.mem_edgeFinset.mp hab
      by_cases ax : a = x.val
      · subst a
        exact mem_union_right _ (mem_image.mpr ⟨b,mem_inter.mpr
          ⟨(X.mem_neighborFinset x.val b).mpr adj,hb⟩,rfl⟩)
      by_cases bx : b = x.val
      · subst b
        exact mem_union_right _ (mem_image.mpr ⟨a,mem_inter.mpr
          ⟨(X.mem_neighborFinset x.val a).mpr adj.symm,ha⟩,Sym2.eq_swap⟩)
      exact mem_union_left _ (mem_inter.mpr ⟨hab,mk_mem_sym2_iff.mpr
        ⟨mem_erase.mpr ⟨ax,ha⟩,mem_erase.mpr ⟨bx,hb⟩⟩⟩)
  have lost := (card_le_card cover).trans (card_union_le ..)
  have cost : (inside.image (fun y => s(x.val,y))).card ≤ inside.card := card_image_le
  have smaller : (U.erase x.val).card < Nat.find start := hU ▸ card_erase_lt_of_mem x.property
  have thin : (edges (U.erase x.val)).card ≤ q * (U.erase x.val).card := by
    by_contra! h
    exact Nat.find_min start smaller ⟨_,rfl,h⟩
  have change := congrArg (q * ·) (card_erase_add_one x.property)
  simp only [Nat.mul_add,Nat.mul_one] at change
  omega

end E713Core

end

section

open Finset SimpleGraph
namespace E713Tree

private theorem forest_leaf {W : Type*} [Fintype W] [Nonempty W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (forest : G.IsAcyclic) : ∃ v, G.degree v ≤ 1 := by
  classical
  rcases subsingleton_or_nontrivial W with hs|hn
  · let _ := hs
    obtain ⟨v⟩ := ‹Nonempty W›
    exact ⟨v,by simp⟩
  let _ := hn
  obtain ⟨T,sub,_,tree⟩ := (connected_top (V := W)).exists_isTree_le_of_le_of_isAcyclic
    (show G ≤ ⊤ from le_top) forest
  obtain ⟨v,hv⟩ := tree.exists_vert_degree_one_of_nontrivial
  exact ⟨v,(G.degree_le_of_le sub).trans hv.le⟩

theorem forest_embedding {W V : Type*} [Fintype W] [Fintype V]
    (G : SimpleGraph W) (X : SimpleGraph V) [DecidableRel X.Adj] (z : V)
    (forest : G.IsAcyclic) (degree : ∀ x, Fintype.card W ≤ X.degree x) : G ⊑ X := by
  classical
  have partialMap (S : Finset W) : ∃ f : W → V, Set.InjOn f (S : Set W) ∧
      ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → X.Adj (f u) (f v) := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases empty : S = ∅
      · subst S
        exact ⟨fun _ => z,by simp,by simp⟩
      obtain ⟨a,ha⟩ := nonempty_iff_ne_empty.mpr empty
      let _ : Nonempty (S : Set W) := ⟨⟨a,ha⟩⟩
      obtain ⟨leaf,low⟩ := forest_leaf (G.induce (S : Set W)) (forest.induce _)
      let u := leaf.val
      have hu : u ∈ S := leaf.property
      let T := S.erase u
      obtain ⟨f,inj,mapAdj⟩ := ih T (erase_ssubset hu)
      have unique (v) (hv : v ∈ T) (w) (hw : w ∈ T) (ev : G.Adj u v) (ew : G.Adj u w) :
          v = w := by
        let v' : (S : Set W) := ⟨v,mem_of_mem_erase hv⟩
        let w' : (S : Set W) := ⟨w,mem_of_mem_erase hw⟩
        have l : ((G.induce (S : Set W)).neighborFinset leaf).card ≤ 1 := low
        have eq := card_le_one.mp l v' ((mem_neighborFinset _ _ _).mpr ev)
          w' ((mem_neighborFinset _ _ _).mpr ew)
        exact congrArg Subtype.val eq
      have anchor : ∃ y : V, ∀ v ∈ T, G.Adj u v → f v = y := by
        by_cases has : ∃ v ∈ T, G.Adj u v
        · obtain ⟨v,hv,ev⟩ := has
          exact ⟨f v,fun w hw ew => congrArg f (unique w hw v hv ew ev)⟩
        · exact ⟨z,fun v hv ev => False.elim (has ⟨v,hv,ev⟩)⟩
      obtain ⟨y,hy⟩ := anchor
      have fresh : ∃ b ∈ X.neighborFinset y, b ∉ T.image f := by
        by_contra! h
        have le := (card_le_card (show X.neighborFinset y ⊆ T.image f from h)).trans card_image_le
        have lt : T.card < S.card := card_lt_card (erase_ssubset hu)
        have lim := card_le_univ S
        have deg := degree y
        rw [card_neighborFinset_eq_degree] at le
        omega
      obtain ⟨b,hb,new⟩ := fresh
      have edge : X.Adj y b := (mem_neighborFinset _ _ _).mp hb
      let g (w : W) := if w = u then b else f w
      have old (w : W) (hw : w ∈ S) (ne : w ≠ u) : w ∈ T := mem_erase.mpr ⟨ne,hw⟩
      have different (w) (hw : w ∈ T) : f w ≠ b := fun eq => new (eq ▸ mem_image_of_mem _ hw)
      refine ⟨g,?_,?_⟩
      · intro v hv w hw eq
        by_cases ev : v = u <;> by_cases ew : w = u
        · exact ev.trans ew.symm
        · exact False.elim (different _ (old w hw ew) (by simpa [g,ev,ew] using eq.symm))
        · exact False.elim (different _ (old v hv ev) (by simpa [g,ev,ew] using eq))
        · exact inj (old v hv ev) (old w hw ew) (by simpa [g,ev,ew] using eq)
      · intro v hv w hw e
        by_cases ev : v = u
        · subst v
          have ew : w ≠ u := e.ne.symm
          simp only [g,if_pos rfl,if_neg ew,hy w (old w hw ew) e]
          exact edge.symm
        by_cases ew : w = u
        · subst w
          simp only [g,if_neg ev,if_pos rfl,hy v (old v hv ev) e.symm]
          exact edge
        simpa only [g,if_neg ev,if_neg ew] using mapAdj v (old v hv ev) w (old w hw ew) e
  obtain ⟨f,inj,hom⟩ := partialMap univ
  exact ⟨⟨⟨f,fun {a b} e => hom a (mem_univ _) b (mem_univ _) e⟩,
    fun _ _ eq => inj (mem_univ _) (mem_univ _) eq⟩⟩

private theorem forest_extremal_le_of_core {q n : ℕ} (G : SimpleGraph (Fin q)) (forest : G.IsAcyclic)
    (core : ∀ (X : SimpleGraph (Fin n)) [DecidableRel X.Adj], q*n < X.edgeFinset.card →
      ∃ (U : Finset (Fin n)) (_ : (U : Set (Fin n))),
        ∀ x : (U : Set (Fin n)), q ≤ (X.induce (U : Set (Fin n))).degree x) :
    extremalNumber n G ≤ q*n := by
  classical
  suffices h : extremalNumber (Fintype.card (Fin n)) G ≤ q*n by simpa only [Fintype.card_fin] using h
  apply (extremalNumber_le_iff (V := Fin n) G _).mpr
  intro X _ free
  by_contra! large
  obtain ⟨U,u,deg⟩ := core X large
  have emb := forest_embedding G (X.induce (U : Set (Fin n))) u forest
    (by simpa only [Fintype.card_fin] using deg)
  exact free (emb.trans (Copy.induce X (U : Set (Fin n))).isContained)

end E713Tree

end

section

open SimpleGraph

namespace E713Isolates

private theorem extend_copy {q n : ℕ} (G : SimpleGraph (Fin q)) (X : SimpleGraph (Fin n))
    (hqn : q ≤ n) (c : Copy (G.induce G.support) X) : G ⊑ X := by
  classical
  let f := Fin.castLEEmb hqn
  obtain ⟨σ,extend⟩ := Equiv.Perm.exists_extending_pair
    (fun x : G.support => f x.val) (fun x => c x)
    (f.injective.comp Subtype.val_injective) c.injective
  refine ⟨⟨⟨fun x => σ (f x),?_⟩, σ.injective.comp f.injective⟩⟩
  intro u v h
  have hu := extend ⟨u,h.left_mem_support⟩
  have hv := extend ⟨v,h.right_mem_support⟩
  change X.Adj (σ (f u)) (σ (f v))
  rw [hu,hv]
  exact c.toHom.map_rel' (show (G.induce G.support).Adj ⟨u,h.left_mem_support⟩
    ⟨v,h.right_mem_support⟩ from h)

private theorem extremal_support {q n : ℕ} (G : SimpleGraph (Fin q)) (hqn : q ≤ n) :
    extremalNumber n G = extremalNumber n (G.induce G.support) := by
  classical
  apply le_antisymm _ ((show G.induce G.support ⊑ G from ⟨Copy.induce G _⟩).extremalNumber_le)
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro X _ free
  apply card_edgeFinset_le_extremalNumber
  intro cs
  exact free (extend_copy G X hqn cs.some)

end E713Isolates

end

section

open SimpleGraph
namespace E713Normalize

open scoped Classical in
theorem normalize {q : ℕ} (G : SimpleGraph (Fin q)) (bip : G.IsBipartite)
    (edges : 2 ≤ G.edgeFinset.card) :
    ∃ (t : ℕ) (F : SimpleGraph (Fin t)), F.IsBipartite ∧ 2 ≤ F.edgeFinset.card ∧
      (∀ v, ¬ F.IsIsolated v) ∧ (∀ n ≥ q, extremalNumber n G = extremalNumber n F) := by
  classical
  let Y := G.induce G.support
  let t := Fintype.card G.support
  let e : G.support ≃ Fin t := Fintype.equivFin _
  let F := Y.map e
  let iso : Y ≃g F := Iso.map e Y
  have bY : Y.IsBipartite := Colorable.of_hom (Copy.induce G G.support).toHom bip
  have cY : Y.edgeFinset.card = G.edgeFinset.card := card_edgeFinset_induce_support
  refine ⟨t,F,Colorable.of_hom iso.symm.toHom bY,?_,?_,?_⟩
  · apply (edges.trans_eq cY.symm).trans_eq
    exact @Iso.card_edgeFinset_eq _ _ _ _ iso _
      (@fintypeEdgeSet (Fin t) F Sym2.instFintype (fun a b => Classical.propDecidable (F.Adj a b)))
  · intro i
    obtain ⟨u,rfl⟩ := iso.surjective i
    obtain ⟨w,huw⟩ := G.mem_support.mp u.property
    let v : G.support := ⟨w,huw.right_mem_support⟩
    exact (iso.toHom.map_rel' (show Y.Adj u v from huw)).not_isIsolated_left
  · intro n hn
    exact (E713Isolates.extremal_support G hn).trans (extremalNumber_congr_right iso)

end E713Normalize

end

section

open SimpleGraph Finset
namespace E713Pack

theorem extremal_sum_bound {V W : Type*} [Fintype V] (H : SimpleGraph V) (K : SimpleGraph W)
    (active : ∀ w, ¬ K.IsIsolated w) (n : ℕ) :
    extremalNumber n (H ⊕g K) ≤
      max (extremalNumber n H) (extremalNumber n K + Fintype.card V * n) := by
  classical
  let bound := max (extremalNumber n H) (extremalNumber n K + Fintype.card V * n)
  suffices h : extremalNumber (Fintype.card (Fin n)) (H ⊕g K) ≤ bound by
    simpa only [Fintype.card_fin] using h
  apply (extremalNumber_le_iff (V := Fin n) (H ⊕g K) _).mpr
  intro X _ free
  by_contra! large
  have lH : extremalNumber n H < X.edgeFinset.card := (le_max_left ..).trans_lt large
  have lK : extremalNumber n K + Fintype.card V*n < X.edgeFinset.card :=
    (le_max_right ..).trans_lt large
  obtain ⟨f⟩ := IsContained.of_extremalNumber_lt_card_edgeFinset (G := X) (H := H)
    (by simpa only [Fintype.card_fin] using lH)
  let D := (univ : Finset V).biUnion (fun v => X.incidenceFinset (f v))
  have subsetD : D ⊆ X.edgeFinset := by
    intro e he
    obtain ⟨v,_,hm⟩ := mem_biUnion.mp he
    exact X.incidenceFinset_subset _ hm
  have cap : D.card ≤ Fintype.card V * n := by
    apply card_biUnion_le.trans
    calc
      _ ≤ ∑ _ : V, n := sum_le_sum (fun v _ => by
        rw [card_incidenceFinset_eq_degree]
        simpa only [Fintype.card_fin] using (X.degree_lt_card_verts (f v)).le)
      _ = _ := by simp
  let Y := X.deleteEdges (D : Set (Sym2 (Fin n)))
  have cardY : Y.edgeFinset.card = X.edgeFinset.card - D.card := by
    rw [show Y.edgeFinset = X.edgeFinset \ D from X.edgeFinset_deleteEdges D,card_sdiff_of_subset subsetD]
  obtain ⟨g⟩ := IsContained.of_extremalNumber_lt_card_edgeFinset (G := Y) (H := K)
    (by rw [Fintype.card_fin,cardY]; omega)
  have apart (v : V) (w : W) : f v ≠ g w := by
    intro eq
    obtain ⟨w',hw⟩ := exists_adj_iff_not_isIsolated.mpr (active w)
    have eg : Y.Adj (g w) (g w') := g.toHom.map_rel' hw
    obtain ⟨adj,kept⟩ := deleteEdges_adj.mp eg
    apply kept
    apply mem_biUnion.mpr
    refine ⟨v,mem_univ _,?_⟩
    rw [mem_incidenceFinset,mk'_mem_incidenceSet_iff]
    exact ⟨adj,Or.inl eq⟩
  let label : V ⊕ W → Fin n := Sum.elim (fun v => f v) (fun w => g w)
  have inj : Function.Injective label := by
    rintro (v|w) (v'|w') eq
    · exact congrArg Sum.inl (f.injective eq)
    · exact (apart _ _ eq).elim
    · exact (apart _ _ eq.symm).elim
    · exact congrArg Sum.inr (g.injective eq)
  apply free
  refine ⟨⟨⟨label,?_⟩,inj⟩⟩
  rintro (v|w) (v'|w') adj
  · exact f.toHom.map_rel' (sum_adj_inl.mp adj)
  · exact False.elim (not_adj_sum_inl_inr v w' adj)
  · exact False.elim (not_adj_sum_inl_inr v' w adj.symm)
  · exact deleteEdges_adj.mp (g.toHom.map_rel' (sum_adj_inr.mp adj)) |>.1

theorem extremal_sum_le {V W : Type*} [Fintype V] (H : SimpleGraph V) (K : SimpleGraph W)
    (active : ∀ w, ¬ K.IsIsolated w) (n : ℕ) :
    extremalNumber n (H ⊕g K) ≤ max (extremalNumber n H) (extremalNumber n K) + Fintype.card V*n := by
  apply (extremal_sum_bound H K active n).trans
  exact max_le (by omega) (by omega)

end E713Pack

end

section

open SimpleGraph Finset
open scoped Classical

namespace E713Split

private theorem sameCard {W : Type*} (a b : Fintype W) : @Fintype.card W a = @Fintype.card W b :=
  @Fintype.card_congr W W a b (Equiv.refl W)

private theorem numbered_side {V : Type*} [Fintype V] (G : SimpleGraph V)
    (bip : G.IsBipartite) (active : ∀ v, ¬ G.IsIsolated v) (S : Set V)
    (closed : ∀ ⦃u v⦄, u ∈ S → G.Adj u v → v ∈ S) :
    ∃ F : SimpleGraph (Fin (Fintype.card S)), F.IsBipartite ∧
      (∀ v, ¬ F.IsIsolated v) ∧ Nonempty (F ≃g G.induce S) := by
  let e := (Fintype.equivFin S).symm
  let F := (G.induce S).comap e
  let f : F →g G := ⟨fun v => (e v).val,fun h => h⟩
  refine ⟨F,⟨bip.some.comp f⟩,?_,⟨SimpleGraph.Iso.comap e (G.induce S)⟩⟩
  intro v
  obtain ⟨w,hw⟩ := exists_adj_iff_not_isIsolated.mpr (active (e v).val)
  have hs : w ∈ S := closed (e v).property hw
  apply exists_adj_iff_not_isIsolated.mp
  refine ⟨e.symm ⟨w,hs⟩,?_⟩
  change G.Adj (e v).val (e (e.symm ⟨w,hs⟩)).val
  simpa using hw

theorem split {V : Type*} [Fintype V] (G : SimpleGraph V) (inh : Nonempty V)
    (bip : G.IsBipartite) (disconnected : ¬ G.Connected) (active : ∀ v, ¬ G.IsIsolated v) :
    ∃ (a b : ℕ) (F : SimpleGraph (Fin a)) (K : SimpleGraph (Fin b)),
      a < Fintype.card V ∧ b < Fintype.card V ∧ F.IsBipartite ∧ K.IsBipartite ∧
      (∀ v, ¬ F.IsIsolated v) ∧ (∀ v, ¬ K.IsIsolated v) ∧ Nonempty ((F ⊕g K) ≃g G) := by
  classical
  obtain ⟨s⟩ := inh
  have missing : ∃ t, ¬ G.Reachable s t := by
    by_contra! h
    exact disconnected ((G.connected_iff_exists_forall_reachable).mpr ⟨s,h⟩)
  obtain ⟨t,ht⟩ := missing
  let S : Set V := G.Reachable s
  have propagate {a b : V} (h : G.Adj a b) : a ∈ S ↔ b ∈ S :=
    ⟨fun ha => ha.trans h.reachable,fun hb => hb.trans h.symm.reachable⟩
  have ls : Fintype.card S < Fintype.card V :=
    Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective (b := t)
      (fun ⟨y,eq⟩ => ht (eq ▸ y.property))
  have rs : Fintype.card (Sᶜ : Set V) < Fintype.card V :=
    Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective (b := s)
      (fun ⟨y,eq⟩ => y.property (eq ▸ SimpleGraph.Reachable.refl (G := G) s))
  obtain ⟨F,bc,ac,⟨e⟩⟩ := numbered_side G bip active S (fun {_ _} ha h => (propagate h).mp ha)
  obtain ⟨K,bd,ad,⟨d⟩⟩ := numbered_side G bip active Sᶜ
    (fun {_ _} ha h hb => ha ((propagate h).mpr hb))
  let glue : G.induce S ⊕g G.induce Sᶜ ≃g G := {
    toEquiv := Equiv.sumCompl (· ∈ S)
    map_rel_iff' := by
      rintro (a|a) (b|b)
      · rfl
      · have noEdge : ¬ G.Adj a.val b.val := fun h => b.property ((propagate h).mp a.property)
        change G.Adj a.val b.val ↔ (false : Bool) = true
        simpa using noEdge
      · have noEdge : ¬ G.Adj a.val b.val := fun h => a.property ((propagate h).mpr b.property)
        change G.Adj a.val b.val ↔ (false : Bool) = true
        simpa using noEdge
      · rfl }
  exact ⟨_,_,F,K,ls,(sameCard _ _).trans_lt rs,bc,bd,ac,ad,⟨(e.sumCongr d).trans glue⟩⟩

theorem extremal_small {V : Type*} [Fintype V] (G : SimpleGraph V)
    (active : ∀ v, ¬ G.IsIsolated v) (atMost : G.edgeFinset.card ≤ 1) (n : ℕ) :
    extremalNumber n G = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  rw [← Fintype.card_fin n,extremalNumber_le_iff]
  intro X _ free
  by_contra! positive
  obtain ⟨edge,he⟩ := card_pos.mp positive
  obtain ⟨u,v,uv⟩ : ∃ u v, X.Adj u v := by
    induction edge using Sym2.ind with
    | _ u v => exact ⟨u,v,X.mem_edgeFinset.mp he⟩
  apply free
  rcases isEmpty_or_nonempty V with hV | hV
  · have : IsEmpty V := hV
    exact ⟨⟨⟨fun _ => u,fun {x} => isEmptyElim x⟩,fun {x} => isEmptyElim x⟩⟩
  let a := Classical.choice hV
  obtain ⟨b,ab⟩ := exists_adj_iff_not_isIsolated.mpr (active a)
  have ends (x : V) : x = a ∨ x = b := by
    obtain ⟨y,xy⟩ := exists_adj_iff_not_isIsolated.mpr (active x)
    have same := card_le_one.mp atMost s(x,y) (G.mem_edgeFinset.mpr xy) s(a,b) (G.mem_edgeFinset.mpr ab)
    exact (Sym2.eq_iff.mp same).elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  let f (x : V) := if x = a then u else v
  have inj : Function.Injective f := by
    intro x y eq
    by_cases xa : x = a
    · by_cases ya : y = a
      · exact xa.trans ya.symm
      · exact (uv.ne (by simpa [f,xa,ya] using eq)).elim
    · by_cases ya : y = a
      · exact (uv.ne.symm (by simpa [f,xa,ya] using eq)).elim
      · exact ((ends x).resolve_left xa).trans ((ends y).resolve_left ya).symm
  refine ⟨⟨⟨f,?_⟩,inj⟩⟩
  intro x y xy
  by_cases xa : x = a
  · have ya : y ≠ a := fun h => xy.ne (xa.trans h.symm)
    simpa [f,xa,ya] using uv
  · have xb := (ends x).resolve_left xa
    have ya : y = a := (ends y).resolve_right (fun h => xy.ne (xb.trans h.symm))
    simpa [f,xa,ya] using uv.symm

end E713Split

end

section

open Filter Asymptotics
open scoped Topology

namespace E713Max

private theorem power_ratio (u v : ℝ) (huv : u ≤ v) :
    Tendsto (fun n : ℕ => (n:ℝ)^u / (n:ℝ)^v) atTop (𝓝 (if u=v then 1 else 0)) := by
  by_cases he : u=v
  · subst v
    simp only [if_true]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    exact (div_self (Real.rpow_pos_of_pos (by exact_mod_cast hn) u).ne').symm
  · rw [if_neg he]
    have hgap : 0 < v-u := sub_pos.mpr (lt_of_le_of_ne huv he)
    have t := (tendsto_rpow_neg_atTop hgap).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
    apply t.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    change (n:ℝ)^(-(v-u)) = (n:ℝ)^u / (n:ℝ)^v
    rw [neg_sub, Real.rpow_sub (by exact_mod_cast hn)]

private theorem normalized (f : ℕ → ℕ) (a u v : ℝ) (huv : u ≤ v)
    (hf : IsEquivalent atTop (fun n : ℕ => (f n:ℝ)) (fun n => a*(n:ℝ)^u)) :
    Tendsto (fun n : ℕ => (f n:ℝ)/(n:ℝ)^v) atTop (𝓝 (if u=v then a else 0)) := by
  have same : IsEquivalent atTop (fun n : ℕ => (n:ℝ)^v) (fun n : ℕ => (n:ℝ)^v) :=
    IsEquivalent.refl
  apply (hf.div same).symm.tendsto_nhds
  have t := (power_ratio u v huv).const_mul a
  simpa only [mul_ite, mul_one, mul_zero, Pi.div_def, mul_div_assoc] using t

private theorem from_limits (f g h : ℕ → ℕ) (q : ℕ) (a b γ : ℝ)
    (hγ : 1 < γ) (hp : 0 < max a b)
    (tf : Tendsto (fun n : ℕ => (f n:ℝ)/(n:ℝ)^γ) atTop (𝓝 a))
    (tg : Tendsto (fun n : ℕ => (g n:ℝ)/(n:ℝ)^γ) atTop (𝓝 b))
    (sandwich : ∀ᶠ n in atTop, max (f n) (g n) ≤ h n ∧ h n ≤ max (f n) (g n) + q*n) :
    IsEquivalent atTop (fun n : ℕ => (h n:ℝ)) (fun n => max a b*(n:ℝ)^γ) := by
  let c := max a b
  have tm := tf.max tg
  let m (n : ℕ) := max (f n) (g n)
  have tmax : Tendsto (fun n : ℕ => (m n:ℝ)/(n:ℝ)^γ) atTop (𝓝 c) := by
    apply tm.congr'
    filter_upwards with n
    change max ((f n:ℝ)/(n:ℝ)^γ) ((g n:ℝ)/(n:ℝ)^γ) = (m n:ℝ)/(n:ℝ)^γ
    have hz : 0 ≤ (n:ℝ)^γ := Real.rpow_nonneg (by positivity) _
    rcases le_total (f n) (g n) with hl | hl
    · have hreal : (f n:ℝ) ≤ g n := by exact_mod_cast hl
      simp only [m, max_eq_right hl, max_eq_right (div_le_div_of_nonneg_right hreal hz)]
    · have hreal : (g n:ℝ) ≤ f n := by exact_mod_cast hl
      simp only [m, max_eq_left hl, max_eq_left (div_le_div_of_nonneg_right hreal hz)]
  have terr : Tendsto (fun n : ℕ => (q:ℝ)*n/(n:ℝ)^γ) atTop (𝓝 0) := by
    have t := (power_ratio 1 γ hγ.le).const_mul (q:ℝ)
    simpa only [if_neg hγ.ne, mul_zero, Real.rpow_one, mul_div_assoc] using t
  have tend : Tendsto (fun n : ℕ => (h n:ℝ)/(n:ℝ)^γ) atTop (𝓝 c) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tmax (by simpa using tmax.add terr)
    · filter_upwards [sandwich] with n hn
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (by positivity) γ)
      exact_mod_cast hn.1
    · filter_upwards [sandwich] with n hn
      change (h n:ℝ)/(n:ℝ)^γ ≤ (m n:ℝ)/(n:ℝ)^γ + (q:ℝ)*n/(n:ℝ)^γ
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (by positivity) γ)
      exact_mod_cast hn.2
  apply isEquivalent_of_tendsto_one
  have t := tend.div_const c
  rw [div_self hp.ne'] at t
  apply t.congr'
  filter_upwards with n
  change (h n:ℝ)/(n:ℝ)^γ/c = (h n:ℝ)/(c*(n:ℝ)^γ)
  rw [div_div,mul_comm]

/-- For unequal exponents the larger exponent's coefficient survives. At a tie the
coefficient is the larger coefficient. -/
theorem max_power_law (f g h : ℕ → ℕ) (q : ℕ) (a b α β : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hγ : 1 < max α β)
    (hf : IsEquivalent atTop (fun n : ℕ => (f n:ℝ)) (fun n => a*(n:ℝ)^α))
    (hg : IsEquivalent atTop (fun n : ℕ => (g n:ℝ)) (fun n => b*(n:ℝ)^β))
    (sandwich : ∀ᶠ n in atTop, max (f n) (g n) ≤ h n ∧ h n ≤ max (f n) (g n) + q*n) :
    let c := if α<β then b else if β<α then a else max a b
    0 < c ∧ IsEquivalent atTop (fun n : ℕ => (h n:ℝ)) (fun n => c*(n:ℝ)^(max α β)) := by
  let γ := max α β
  let c := if α<β then b else if β<α then a else max a b
  have hp : 0 < c := by
    dsimp [c]
    split_ifs <;> positivity
  have hc : max (if α=γ then a else 0) (if β=γ then b else 0) = c := by
    rcases lt_trichotomy α β with h | h | h
    · simp [c,γ,max_eq_right h.le,h,h.ne, hb.le]
    · subst β
      simp [c,γ]
    · simp [c,γ,max_eq_left h.le,h,h.ne, h.not_gt,ha.le]
  have tf := normalized f a α γ (le_max_left _ _) hf
  have tg := normalized g b β γ (le_max_right _ _) hg
  exact ⟨hp, by simpa only [hc] using from_limits f g h q _ _ γ hγ (hc ▸ hp) tf tg sandwich⟩

/-- A merely linear component contributes zero at a superlinear normalization. -/
theorem mixed_max_power_law (f g h : ℕ → ℕ) (q C : ℕ) (b β : ℝ)
    (hb : 0 < b) (hβ : 1 < β) (bounded : ∀ᶠ n in atTop, f n ≤ C*n)
    (hg : IsEquivalent atTop (fun n : ℕ => (g n:ℝ)) (fun n => b*(n:ℝ)^β))
    (sandwich : ∀ᶠ n in atTop, max (f n) (g n) ≤ h n ∧ h n ≤ max (f n) (g n) + q*n) :
    IsEquivalent atTop (fun n : ℕ => (h n:ℝ)) (fun n => b*(n:ℝ)^β) := by
  have tlin : Tendsto (fun n : ℕ => (C:ℝ)*n/(n:ℝ)^β) atTop (𝓝 0) := by
    simpa only [if_neg hβ.ne, mul_zero, Real.rpow_one, mul_div_assoc] using
      (power_ratio 1 β hβ.le).const_mul (C:ℝ)
  have tf : Tendsto (fun n : ℕ => (f n:ℝ)/(n:ℝ)^β) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x:=0)) tlin
    · filter_upwards with n
      positivity
    · filter_upwards [bounded] with n hn
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (by positivity) β)
      exact_mod_cast hn
  have tg : Tendsto (fun n : ℕ => (g n:ℝ)/(n:ℝ)^β) atTop (𝓝 b) := by
    simpa only [if_true] using normalized g b β β le_rfl hg
  simpa only [max_eq_right hb.le] using from_limits f g h q 0 b β hβ
    (lt_max_of_lt_right hb) tf tg sandwich

/-- A power law of exponent one has an eventual linear bound with a natural coefficient. -/
theorem eventually_linear_of_power_one (f : ℕ → ℕ) (a : ℝ)
    (hf : IsEquivalent atTop (fun n : ℕ => (f n:ℝ)) (fun n => a*(n:ℝ)^(1:ℝ))) :
    ∃ C : ℕ, ∀ᶠ n in atTop, f n ≤ C*n := by
  have t : Tendsto (fun n : ℕ => (f n:ℝ)/n) atTop (𝓝 a) := by
    simpa only [if_true, Real.rpow_one] using normalized f a 1 1 le_rfl hf
  obtain ⟨C,hC⟩ := exists_nat_gt a
  refine ⟨C, ?_⟩
  filter_upwards [t.eventually (gt_mem_nhds hC), eventually_gt_atTop (0:ℕ)] with n hn hpos
  have ht : (f n:ℝ) < (C:ℝ)*n := (div_lt_iff₀ (by exact_mod_cast hpos)).mp hn
  exact_mod_cast ht.le

end E713Max

end

section

open SimpleGraph Finset
open scoped Classical

namespace E713MatchingIso

theorem matching_iso {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (regular : ∀ v, G.degree v = 1)
    {k : ℕ} (hk : G.edgeFinset.card = k) :
    ∃ M : SimpleGraph (Fin k × Bool),
      (∀ x y, M.Adj x y ↔ x.1 = y.1 ∧ x.2 ≠ y.2) ∧ Nonempty (M ≃g G) := by
  let number : Fin k ≃ G.edgeFinset := (Finset.equivFinOfCardEq hk).symm
  let endpt (e : G.edgeFinset) : Bool ≃ e.val.toFinset :=
    finTwoEquiv.symm.trans (Finset.equivFinOfCardEq (G.card_toFinset_mem_edgeFinset e)).symm
  let f (p : Fin k × Bool) : V := (endpt (number p.1) p.2).val
  have incident (p : Fin k × Bool) : (number p.1).val ∈ G.incidenceFinset (f p) :=
    (G.mem_incidenceFinset _ _).mpr ⟨G.mem_edgeFinset.mp (number p.1).property,
      Sym2.mem_toFinset.mp (endpt (number p.1) p.2).property⟩
  have unique (x : V) : ∀ e ∈ G.incidenceFinset x, ∀ d ∈ G.incidenceFinset x, e = d := by
    apply card_le_one.mp
    rw [card_incidenceFinset_eq_degree,regular]
  have inj : Function.Injective f := by
    rintro ⟨i,a⟩ ⟨j,b⟩ eq
    have ie := incident (i,a)
    rw [eq] at ie
    have same : (number i).val = (number j).val := unique _ _ ie _ (incident (j,b))
    have ij := number.injective (Subtype.ext same)
    subst j
    have ab := (endpt (number i)).injective (Subtype.ext eq)
    exact congrArg (Prod.mk i) ab
  have surj : Function.Surjective f := by
    intro x
    obtain ⟨e,he⟩ := card_pos.mp (by rw [card_incidenceFinset_eq_degree,regular]; decide :
      0 < (G.incidenceFinset x).card)
    let E : G.edgeFinset := ⟨e,G.incidenceFinset_subset x he⟩
    obtain ⟨i,hi⟩ := number.surjective E
    have hx : x ∈ (number i).val.toFinset := by
      rw [hi]
      exact Sym2.mem_toFinset.mpr ((G.mem_incidenceFinset _ _).mp he).2
    exact ⟨(i,(endpt (number i)).symm ⟨x,hx⟩),congrArg Subtype.val ((endpt (number i)).apply_symm_apply _)⟩
  let e := Equiv.ofBijective f ⟨inj,surj⟩
  refine ⟨G.comap e,?_,⟨SimpleGraph.Iso.comap e G⟩⟩
  intro p q
  change G.Adj (f p) (f q) ↔ _
  constructor
  · intro h
    have edgep : s(f p,f q) ∈ G.incidenceFinset (f p) :=
      (G.mem_incidenceFinset _ _).mpr (G.mk'_mem_incidenceSet_left_iff.mpr h)
    have edgeq : s(f p,f q) ∈ G.incidenceFinset (f q) :=
      (G.mem_incidenceFinset _ _).mpr (G.mk'_mem_incidenceSet_right_iff.mpr h)
    have index : p.1 = q.1 := number.injective (Subtype.ext
      ((unique _ _ (incident p) _ edgep).trans (unique _ _ edgeq _ (incident q))))
    exact ⟨index,fun same => h.ne (congrArg f (Prod.ext index same))⟩
  · rintro ⟨index,different⟩
    have ne : f p ≠ f q := fun same => different (congrArg Prod.snd (inj same))
    have hi := (G.mem_incidenceFinset _ _).mp (incident p)
    have hj := (G.mem_incidenceFinset _ _).mp (incident q)
    rw [← index] at hj
    exact G.adj_of_mem_incidenceSet ne hi hj

end E713MatchingIso

end

section

open Finset SimpleGraph
open scoped Sym2

namespace E713MatchingUpper

/-- A graph on n vertices whose matchings have at most m edges has at most mn edges. -/
theorem edge_bound {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ)
    (bound : ∀ E ⊆ G.edgeFinset,
      (∀ e ∈ E, ∀ d ∈ E, ∀ x : V, x ∈ e → x ∈ d → e=d) → E.card ≤ m) :
    G.edgeFinset.card ≤ m * Fintype.card V := by
  classical
  let label := Fintype.equivFin V
  let col : Sym2 V → Fin (Fintype.card V) :=
    Sym2.lift ⟨fun x y => label x + label y, fun x y => add_comm _ _⟩
  have unique (c : Fin (Fintype.card V)) (e d : Sym2 V) (he : col e = c) (hd : col d = c)
      (x : V) (hx : x∈e) (hy : x∈d) : e=d := by
    have a : label x + label (Sym2.Mem.other hx) = c := by
      change col s(x,Sym2.Mem.other hx) = c
      rw [Sym2.other_spec hx, he]
    have b : label x + label (Sym2.Mem.other hy) = c := by
      change col s(x,Sym2.Mem.other hy) = c
      rw [Sym2.other_spec hy, hd]
    have hu := label.injective (add_left_cancel (a.trans b.symm))
    rw [← Sym2.other_spec hx, ← Sym2.other_spec hy, hu]
  calc
    G.edgeFinset.card = ∑ c : Fin (Fintype.card V), (G.edgeFinset.filter fun e => col e = c).card :=
      Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_univ _
    _ ≤ ∑ _c : Fin (Fintype.card V), m := by
      refine Finset.sum_le_sum fun c _ => bound _ (Finset.filter_subset _ _) ?_
      exact fun e he d hd => unique c e d (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hd).2
    _ = m * Fintype.card V := by simp [mul_comm]

/-- An indexed list of k disjoint graph edges supplies a copy of the k-edge matching. -/
private theorem matching_copy {k : ℕ} {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (M : SimpleGraph (Fin k × Bool))
    (pattern : ∀ x y, M.Adj x y ↔ x.1=y.1 ∧ x.2≠y.2)
    (E : Finset (Sym2 V)) (edges : E ⊆ G.edgeFinset)
    (unique : ∀ e ∈ E, ∀ d ∈ E, ∀ x : V, x∈e → x∈d → e=d)
    (hk : k ≤ E.card) : M ⊑ G := by
  classical
  let idx : Fin k ↪ E := (Fin.castLEEmb hk).trans E.equivFin.symm.toEmbedding
  have endpoints (i : Fin k) : ∃ x y : V, s(x,y) = (idx i).val :=
    Sym2.inductionOn (idx i).val fun x y => ⟨x,y,rfl⟩
  choose a b ep using endpoints
  have adj (i : Fin k) : G.Adj (a i) (b i) := by
    have mem := edges (idx i).property
    rw [← ep i] at mem
    exact G.mem_edgeFinset.mp mem
  let v (z : Fin k × Bool) := if z.2 then b z.1 else a z.1
  have member (i : Fin k) (j : Bool) : v (i,j) ∈ (idx i).val := by
    rw [← ep]
    cases j <;> simp [v]
  let hom : M →g G := ⟨v, by
    rintro ⟨i,u⟩ ⟨j,w⟩ h
    obtain ⟨rfl,hne⟩ := (pattern _ _).mp h
    cases u <;> cases w <;> simp_all [v, G.adj_comm]⟩
  refine ⟨hom.toCopy ?_⟩
  rintro ⟨i,u⟩ ⟨j,w⟩ he
  change v (i,u) = v (j,w) at he
  have hsame := unique _ (idx i).property _ (idx j).property (v (i,u))
    (member i u) (he ▸ member j w)
  obtain rfl := idx.injective (Subtype.ext hsame)
  have hne := (adj i).ne
  cases u <;> cases w <;> simp_all [v]

/-- The extremal number for a k-edge matching is bounded by (k-1)n, uniformly in n. -/
theorem matching_upper {k : ℕ} (M : SimpleGraph (Fin k × Bool))
    (pattern : ∀ x y, M.Adj x y ↔ x.1=y.1 ∧ x.2≠y.2) (n : ℕ) :
    extremalNumber n M ≤ (k-1)*n := by
  classical
  have h : extremalNumber (Fintype.card (Fin n)) M ≤ (k-1)*n := by
    apply (extremalNumber_le_iff M _).mpr
    intro G _ free
    have bound := edge_bound G (k-1) (by
      intro E hE hmatching
      by_contra! hbad
      exact free (matching_copy G M pattern E hE hmatching (by omega)))
    simpa only [Fintype.card_fin] using bound
  simpa using h

end E713MatchingUpper

end

section

open SimpleGraph Finset
namespace E713MatchLower

theorem matching_lower {k : ℕ} (M : SimpleGraph (Fin k × Bool))
    (matching : ∀ x y, M.Adj x y ↔ x.1 = y.1 ∧ x.2 ≠ y.2)
    (n : ℕ) (hn : k-1 ≤ n) :
    (k-1)*(n-(k-1)) ≤ extremalNumber n M := by
  classical
  by_cases zero : k=0
  · simp [zero]
  let A := Fin (k-1)
  let B := Fin (n-(k-1))
  let X := completeBipartiteGraph A B
  have free : M.Free X := by
    rintro ⟨f⟩
    have hit (i : Fin k) : ∃ (a : A) (b : Bool), f (i,b) = Sum.inl a := by
      have e : M.Adj (i,false) (i,true) := (matching _ _).mpr ⟨rfl,by simp⟩
      have h := f.toHom.map_rel' e
      change X.Adj (f (i,false)) (f (i,true)) at h
      cases hl : f (i,false) with
      | inl a => exact ⟨a,false,hl⟩
      | inr b =>
        cases hr : f (i,true) with
        | inl a => exact ⟨a,true,hr⟩
        | inr c => simp [hl,hr,X,completeBipartiteGraph_adj] at h
    choose part endpoint which using hit
    have inj : Function.Injective part := by
      intro i j eq
      have h : f (i,endpoint i) = f (j,endpoint j) :=
        (which i).trans ((congrArg Sum.inl eq).trans (which j).symm)
      exact congrArg Prod.fst (f.injective h)
    have impossible := Fintype.card_le_of_injective part inj
    simp only [A,Fintype.card_fin] at impossible
    omega
  let edge (u : A × B) : X.edgeSet := ⟨s(Sum.inl u.1,Sum.inr u.2),by
    simp [X,completeBipartiteGraph_adj]⟩
  have inj : Function.Injective edge := by
    rintro ⟨a,b⟩ ⟨c,d⟩ eq
    obtain h|h := Sym2.eq_iff.mp (congrArg Subtype.val eq)
    · exact Prod.ext (Sum.inl.inj h.1) (Sum.inr.inj h.2)
    · cases h.1
  have count := Fintype.card_le_of_injective edge inj
  rw [← X.edgeFinset_card] at count
  simp only [A,B,Fintype.card_prod,Fintype.card_fin] at count
  have size : Fintype.card (A ⊕ B) = n := by
    simp only [A,B,Fintype.card_sum,Fintype.card_fin]
    omega
  have bound := card_edgeFinset_le_extremalNumber free
  rw [size] at bound
  exact count.trans bound

end E713MatchLower

end

section

open Filter Asymptotics
open scoped Topology

namespace E713MatchLimit

private theorem linear {a : ℕ → ℕ} {k : ℕ} (hk : 0 < k)
    (lo : ∀ n, k ≤ n → k*(n-k) ≤ a n) (hi : ∀ n, a n ≤ k*n) :
    IsEquivalent atTop (fun n : ℕ => (a n : ℝ)) (fun n => (k:ℝ)*n) := by
  have pk : (0 : ℝ) < k := by exact_mod_cast hk
  have small : Tendsto (fun n : ℕ => (k:ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have left : Tendsto (fun n : ℕ => 1 - (k:ℝ)/n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub small
  apply isEquivalent_of_tendsto_one
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' left tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop k] with n hn
    have pn : (0 : ℝ)<n := by exact_mod_cast (hk.trans_le hn)
    have hc : (k:ℝ) * (n-k:ℕ) ≤ (a n:ℝ) := by exact_mod_cast (lo n hn)
    rw [Nat.cast_sub hn] at hc
    change 1-(k:ℝ)/n ≤ (a n:ℝ)/((k:ℝ)*n)
    apply (le_div_iff₀ (mul_pos pk pn)).mpr
    calc
      (1-(k:ℝ)/n)*((k:ℝ)*n) = (k:ℝ)*(n-k) := by field_simp
      _ ≤ _ := hc
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have pn : (0 : ℝ)<n := by exact_mod_cast hn
    change (a n:ℝ)/((k:ℝ)*n) ≤ 1
    rw [div_le_iff₀ (mul_pos pk pn),one_mul]
    exact_mod_cast hi n

end E713MatchLimit

end

open SimpleGraph Asymptotics Filter Set
open scoped Classical Topology

namespace OMA.R_Erdos713_erdos_713_parts_i_R1

/-- Connected graphs containing a cycle whose extremal numbers per vertex tend to infinity. -/
def H1 : Prop := ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → 2 ≤ G.edgeFinset.card →
  (∀ v, ¬ G.IsIsolated v) → G.Connected → ¬ G.IsAcyclic →
  Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / n) atTop atTop →
  ∃ α c : ℝ, α ∈ Ioo 1 2 ∧ 0 < c ∧ IsEquivalent atTop
    (fun n : ℕ => (extremalNumber n G : ℝ)) (fun n => c * (n:ℝ)^α)

/-- Disconnected graphs with no isolated vertices, a vertex of degree at least two, and
eventually at most linearly many edges in the extremal host. -/
def H2 : Prop := ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → 2 ≤ G.edgeFinset.card →
  (∀ v, ¬ G.IsIsolated v) → ¬ G.Connected → (∃ v, 2 ≤ G.degree v) →
  (∃ C : ℕ, ∀ᶠ n : ℕ in atTop, extremalNumber n G ≤ C*n) →
  ∃ c : ℝ, 0 < c ∧ IsEquivalent atTop
    (fun n : ℕ => (extremalNumber n G : ℝ)) (fun n => c * n)

section

set_option maxHeartbeats 1500000 in
theorem main : H1 → H2 → type_of% @Erdos713.erdos_713.parts.i := by
  intro connectedCase linearCase q G bip edges
  classical
  let Goal (a : ℕ → ℕ) : Prop := ∃ α c : ℝ, α ∈ Ico 1 2 ∧ 0 < c ∧
    IsEquivalent atTop (fun n : ℕ => (a n : ℝ)) (fun n => c*(n:ℝ)^α)
  let Bound (a : ℕ → ℕ) : Prop := ∃ C : ℕ, ∀ᶠ n in atTop, a n ≤ C*n
  let Power (a : ℕ → ℕ) : Prop := ∃ α c : ℝ, α ∈ Ioo 1 2 ∧ 0 < c ∧
    IsEquivalent atTop (fun n : ℕ => (a n : ℝ)) (fun n => c*(n:ℝ)^α)
  have fromPower {a} (h : Power a) : Goal a := by
    obtain ⟨α,c,hα,hc,fit⟩ := h
    exact ⟨α,c,⟨hα.1.le,hα.2⟩,hc,fit⟩
  have fromLinear {a : ℕ → ℕ} (h : ∃ c : ℝ, 0<c ∧ IsEquivalent atTop
      (fun n : ℕ => (a n : ℝ)) (fun n => c * n)) : Goal a := by
    obtain ⟨c,cp,fit⟩ := h
    exact ⟨1,c,⟨le_rfl,by norm_num⟩,cp,by simpa using fit⟩
  have normalized (k : ℕ) : ∀ (X : SimpleGraph (Fin k)), X.IsBipartite →
      (∀ v, ¬X.IsIsolated v) → 2 ≤ X.edgeFinset.card → Goal (extremalNumber · X) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro X bipX activeX many
      by_cases conn : X.Connected
      · rcases E713Fekete.density_alternative (extremalNumber · X)
            (E713Super.superadditive X conn many) (E713Super.positive_at_two X many) with lin | diverge
        · exact fromLinear lin
        · apply fromPower
          apply connectedCase k X bipX many activeX conn _ diverge
          intro forest
          have bounded (n : ℕ) : extremalNumber n X ≤ k*n := by
            apply E713Tree.forest_extremal_le_of_core X forest
            intro Y _ high
            exact E713Core.dense_core Y k (by simpa only [Fintype.card_fin] using high)
          obtain ⟨n,large,hn⟩ := ((tendsto_atTop.mp diverge ((k:ℝ)+1)).and
            (eventually_ge_atTop (1:ℕ))).exists
          have pos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
          have cap : (extremalNumber n X : ℝ) / n ≤ k := (div_le_iff₀ pos).mpr (by
            exact_mod_cast bounded n)
          linarith
      · have prof {j : ℕ} (sm : j < k) (Y : SimpleGraph (Fin j)) (b : Y.IsBipartite)
            (active : ∀ v, ¬Y.IsIsolated v) : Bound (extremalNumber · Y) ∨ Power (extremalNumber · Y) := by
          by_cases two : 2 ≤ Y.edgeFinset.card
          · obtain ⟨α,c,hα,hc,fit⟩ := ih j sm Y b active two
            rcases hα.1.eq_or_lt with eq | lt
            · subst α
              exact Or.inl (E713Max.eventually_linear_of_power_one _ c fit)
            · exact Or.inr ⟨α,c,⟨lt,hα.2⟩,hc,fit⟩
          · left
            exact ⟨0,Eventually.of_forall (fun n => by simp [E713Split.extremal_small Y active (by omega : Y.edgeFinset.card ≤ 1) n])⟩
        have nonempty : Nonempty (Fin k) := by
          by_contra! empty
          have eq : X = ⊥ := by ext u; exact empty.false u |>.elim
          have zero : X.edgeFinset.card = 0 := by simp [eq]
          omega
        obtain ⟨a,b,F,K,ha,hb,bF,bK,aF,aK,⟨e⟩⟩ := E713Split.split X nonempty bipX conn activeX
        have sand : ∀ᶠ n in atTop, max (extremalNumber n F) (extremalNumber n K) ≤ extremalNumber n X ∧
            extremalNumber n X ≤ max (extremalNumber n F) (extremalNumber n K) + a*n := by
          apply Eventually.of_forall
          intro n
          rw [← extremalNumber_congr_right e]
          refine ⟨max_le (IsContained.extremalNumber_le ⟨(Embedding.sumInl (G := F) (H := K)).toCopy⟩)
            (IsContained.extremalNumber_le ⟨(Embedding.sumInr (G := F) (H := K)).toCopy⟩),?_⟩
          simpa only [Fintype.card_fin] using E713Pack.extremal_sum_le F K aK n
        rcases prof (by simpa using ha) F bF aF with ⟨C,cBound⟩ | ⟨α,c,hα,hc,fc⟩ <;>
          rcases prof (by simpa using hb) K bK aK with ⟨D,dBound⟩ | ⟨β,d,hβ,hd,kd⟩
        · by_cases high : ∃ v, 2 ≤ X.degree v
          swap
          · have one (v) : X.degree v = 1 := by
              have pos := (X.degree_pos_iff_mem_support v).mpr
                (X.mem_support_iff_not_isIsolated.mpr (activeX v))
              have low : ¬ 2 ≤ X.degree v := fun h => high ⟨v,h⟩
              omega
            obtain ⟨M,pattern,⟨equiv⟩⟩ := E713MatchingIso.matching_iso X one rfl
            have pos : 0 < X.edgeFinset.card-1 := by omega
            apply fromLinear
            refine ⟨(X.edgeFinset.card-1 : ℕ),by exact_mod_cast pos,?_⟩
            apply E713MatchLimit.linear pos
            · intro n hn
              rw [← extremalNumber_congr_right equiv]
              exact E713MatchLower.matching_lower M pattern n hn
            · intro n
              rw [← extremalNumber_congr_right equiv]
              exact E713MatchingUpper.matching_upper M pattern n
          apply fromLinear (linearCase k X bipX many activeX conn high ?_)
          refine ⟨max C D + a,?_⟩
          filter_upwards [sand,cBound,dBound] with n sn cf dk
          rw [Nat.add_mul]
          apply sn.2.trans (Nat.add_le_add_right _ _)
          exact max_le (cf.trans (Nat.mul_le_mul_right _ (le_max_left C D)))
            (dk.trans (Nat.mul_le_mul_right _ (le_max_right C D)))
        · apply fromPower
          exact ⟨β,d,hβ,hd,E713Max.mixed_max_power_law _ _ _ a C d β hd hβ.1 cBound kd sand⟩
        · apply fromPower
          refine ⟨α,c,hα,hc,E713Max.mixed_max_power_law _ _ _ a D c α hc hα.1 dBound fc ?_⟩
          simpa only [max_comm] using sand
        · obtain ⟨pos,fit⟩ := E713Max.max_power_law _ _ _ a c d α β hc hd
              (hα.1.trans_le (le_max_left _ _)) fc kd sand
          exact fromPower ⟨max α β,_,⟨hα.1.trans_le (le_max_left _ _),max_lt hα.2 hβ.2⟩,pos,fit⟩
  obtain ⟨t,F,b,sz,act,stable⟩ := E713Normalize.normalize G bip edges
  obtain ⟨α,c,hα,hc,fit⟩ := normalized t F b act sz
  refine ⟨α,c,hα,hc,?_⟩
  apply fit.congr_left
  filter_upwards [eventually_ge_atTop q] with n hn
  exact_mod_cast (stable n hn).symm

end
end OMA.R_Erdos713_erdos_713_parts_i_R1
