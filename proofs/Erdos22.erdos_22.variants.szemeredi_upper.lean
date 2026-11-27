import FormalConjectures.ErdosProblems.«22»
import Mathlib

-- Credit: @marcusbuffett
/- The argument identifying partition cells of a triangle follows the proof in
Mathlib/Combinatorics/SimpleGraph/Triangle/Removal.lean at mathlib4 commit
0df444a360eaa60ab8c11dca51a86af692955474.
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Used under the Apache License, Version 2.0. -/
/-! The Ramsey–Turán upper bound for K₄. For an edge, its common
neighborhood is independent. This bounds both the triangle count and the
density on every cut. Apply triangle removal and cover the remaining
triangle-free graph by a bounded collection of dense regular rectangles.
Filling these rectangles preserves triangle-freeness by the triangle counting
lemma. Mantel's bound controls their total area. -/

namespace Szemeredi22
open Finset SimpleGraph
open scoped Classical

private theorem common_indep {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.CliqueFree 4)
    {a b : Fin n} (hab : G.Adj a b) :
    G.IsIndepSet (G.commonNeighbors a b) := by
  intro x hx y hy _ hxy
  have tri : G.IsNClique 3 {b,x,y} := is3Clique_triple_iff.mpr ⟨hx.2,hy.2,hxy⟩
  exact hG _ (tri.insert (a:=a) (by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hab
    · exact hx.1
    · exact hy.1))

theorem half_cut (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (X Y : Finset (Fin n)) :
    2*(G.interedges X Y).card ≤ X.card*Y.card + 3*G.indepNum*n := by
  classical
  let N := fun x => Y.filter (G.Adj x)
  let heavy := X.filter (fun x => Y.card+G.indepNum < 2*(N x).card)
  have hheavy : G.IsIndepSet (heavy : Set (Fin n)) := by
    intro x hx y hy _ hxy
    have hcx : Y.card+G.indepNum < 2*(N x).card := (mem_filter.mp hx).2
    have hcy : Y.card+G.indepNum < 2*(N y).card := (mem_filter.mp hy).2
    have sub : ↑(N x ∩ N y) ⊆ G.commonNeighbors x y := by
      intro v hv
      exact ⟨(mem_filter.mp (mem_inter.mp hv).1).2,(mem_filter.mp (mem_inter.mp hv).2).2⟩
    have hi : (N x ∩ N y).card ≤ G.indepNum := IsIndepSet.card_le_indepNum (Set.Pairwise.mono sub (common_indep hG hxy))
    have hu : (N x ∪ N y).card ≤ Y.card :=
      card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
    have hc := card_union_add_card_inter (N x) (N y)
    omega
  have hsum : (G.interedges X Y).card = ∑ x ∈ X, (N x).card := by
    simp only [SimpleGraph.interedges_def,N,card_filter,sum_product]
  have hterm (x : Fin n) (hx : x ∈ X) :
      2*(N x).card ≤ Y.card+G.indepNum + (if x ∈ heavy then 2*Y.card else 0) := by
    split_ifs with hh
    · have := card_le_card (filter_subset (G.Adj x) Y)
      change 2*(Y.filter (G.Adj x)).card ≤ _
      omega
    · by_contra! h
      apply hh
      exact mem_filter.mpr ⟨hx,by omega⟩
  have total := sum_le_sum hterm
  rw [← mul_sum,sum_add_distrib] at total
  simp only [sum_const,nsmul_eq_mul,sum_ite_mem] at total
  have sub : heavy ⊆ X := filter_subset _ _
  have hx : X.card ≤ n := by simpa using X.card_le_univ
  have hy : Y.card ≤ n := by simpa using Y.card_le_univ
  have hc := hheavy.card_le_indepNum
  rw [hsum]
  calc
    _ ≤ _ := total
    _ ≤ X.card*Y.card + X.card*G.indepNum + G.indepNum*(2*n) := by
      rw [mul_add]
      simp only [Nat.cast_id,inter_eq_right.mpr sub] at *
      gcongr
    _ ≤ _ := by nlinarith [Nat.mul_le_mul_right G.indepNum hx]

theorem few_triangles (n : ℕ) (G : SimpleGraph (Fin n)) (hg : G.CliqueFree 4) :
    (G.cliqueFinset 3).card ≤ G.indepNum*n^2 := by
  classical
  let edges := (univ : Finset (Fin n × Fin n)).filter (fun e => G.Adj e.1 e.2)
  let fiber := fun e : Fin n × Fin n => univ.filter (fun x => G.Adj e.1 x ∧ G.Adj e.2 x)
  have hsub : G.cliqueFinset 3 ⊆ edges.biUnion (fun e => (fiber e).image (fun z => {e.1,e.2,z})) := by
    intro s hs
    obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := is3Clique_iff.mp (mem_cliqueFinset_iff.mp hs)
    exact mem_biUnion.mpr ⟨(a,b),mem_filter.mpr ⟨mem_univ _,hab⟩,
      mem_image.mpr ⟨c,mem_filter.mpr ⟨mem_univ _,hac,hbc⟩,rfl⟩⟩
  have hc (e : Fin n × Fin n) (he : e ∈ edges) : (fiber e).card ≤ G.indepNum := by
    apply IsIndepSet.card_le_indepNum
    apply Set.Pairwise.mono (s:=G.commonNeighbors e.1 e.2) _ (common_indep hg (mem_filter.mp he).2)
    intro x hx
    exact (mem_filter.mp hx).2
  have he : edges.card ≤ n^2 := by
    simpa [sq] using edges.card_le_univ
  calc
    _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ _e ∈ edges, G.indepNum := sum_le_sum fun e he => card_image_le.trans (hc e he)
    _ = G.indepNum*edges.card := by simp [mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ he

end Szemeredi22

namespace Szemeredi22

open Finset SimpleGraph Filter SzemerediRegularity
open scoped Classical

private def block {n : ℕ} (J : SimpleGraph (Fin n)) (P : Finpartition (univ : Finset (Fin n)))
    (θ : ℝ) (U V : Finset (Fin n)) : Prop :=
  U ∈ P.parts ∧ V ∈ P.parts ∧ U ≠ V ∧ J.IsUniform (θ/8) U V ∧ θ/4 ≤ J.edgeDensity U V

private def blockGraph {n : ℕ} (J : SimpleGraph (Fin n)) (P : Finpartition (univ : Finset (Fin n)))
    (θ : ℝ) : SimpleGraph (Fin n) where
  Adj x y := ∃ U V, block J P θ U V ∧ x ∈ U ∧ y ∈ V
  symm.symm x y := by
    rintro ⟨U,V,⟨hu,hv,huv,hreg,hd⟩,hx,hy⟩
    exact ⟨V,U,⟨hv,hu,huv.symm,hreg.symm,by rwa [J.edgeDensity_comm]⟩,hy,hx⟩
  loopless.irrefl x := by
    rintro ⟨U,V,⟨hu,hv,huv,_,_⟩,hx,hy⟩
    exact disjoint_left.mp (P.disjoint hu hv huv) hx hy

private theorem block_free {n : ℕ} {J : SimpleGraph (Fin n)}
    (P : Finpartition (univ : Finset (Fin n))) {θ : ℝ} (hθ : 0 < θ) (ht : θ ≤ 1)
    (hJ : J.CliqueFree 3) : (blockGraph J P θ).CliqueFree 3 := by
  classical
  intro t ht3
  obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := is3Clique_iff.mp ht3
  obtain ⟨U,V,⟨hu,hv,huv,ruv,duv⟩,hx,hy⟩ := hxy
  obtain ⟨U',W,⟨hu',hw,huw,ruw,duw⟩,hx',hz⟩ := hxz
  obtain ⟨V',W',⟨hv',hw',hvw,rvw,dvw⟩,hy',hz'⟩ := hyz
  obtain rfl : U = U' := P.disjoint.elim hu hu' (not_disjoint_iff.mpr ⟨x,hx,hx'⟩)
  obtain rfl : V = V' := P.disjoint.elim hv hv' (not_disjoint_iff.mpr ⟨y,hy,hy'⟩)
  obtain rfl : W = W' := P.disjoint.elim hw hw' (not_disjoint_iff.mpr ⟨z,hz,hz'⟩)
  have e : 2*(θ/8)=θ/4 := by ring
  have hc := J.triangle_counting (e ▸ duv) ruv (P.disjoint hu hv huv)
    (e ▸ duw) ruw (P.disjoint hu hw huw) (e ▸ dvw) rvw (P.disjoint hv hw hvw)
  have zero : J.cliqueFinset 3 = ∅ := eq_empty_iff_forall_notMem.mpr
    (fun s hs => hJ s (mem_cliqueFinset_iff.mp hs))
  rw [zero,card_empty,Nat.cast_zero] at hc
  have hu0 := card_pos.mpr (show U.Nonempty from ⟨x,hx⟩)
  have hv0 := card_pos.mpr (show V.Nonempty from ⟨y,hy⟩)
  have hw0 := card_pos.mpr (show W.Nonempty from ⟨z,hz⟩)
  have ha : 0 < 1-2*(θ/8) := by linarith
  exact (not_lt_of_ge hc) (by positivity)

private theorem mantel {n : ℕ} (J : SimpleGraph (Fin n)) (h : J.CliqueFree 3) :
    4*J.edgeFinset.card ≤ n^2 := by
  classical
  have hm := h.card_edgeFinset_le (r:=2)
  simp only [Fintype.card_fin, Nat.reduceSub, mul_one, Nat.reduceMul] at hm
  have hmod : n%2 = 0 ∨ n%2 = 1 := by omega
  rcases hmod with hmod | hmod <;> simp [hmod] at hm <;> omega

theorem rectangle_cover (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ᶠ n : ℕ in atTop, ∀ J : SimpleGraph (Fin n), J.CliqueFree 3 →
     ∃ S : Finset (Finset (Fin n) × Finset (Fin n)), S.card ≤ K ∧
      (∑ z ∈ S, (z.1.card : ℝ)*z.2.card) ≤ (n : ℝ)^2/2 ∧
      2*(J.edgeFinset.card : ℝ) ≤ η*n^2 + ∑ z ∈ S, ((J.interedges z.1 z.2).card : ℝ) := by
  classical
  let θ := min (η/2) 1
  have hθ : 0 < θ := lt_min (by positivity) zero_lt_one
  have ht : θ ≤ 1 := min_le_right _ _
  let l := ⌈4/θ⌉₊
  let k := bound (θ/8) l
  use k^2
  filter_upwards [eventually_ge_atTop (max l 1)] with n hn J hJ
  have hn' : 0 < n := (le_max_right _ _).trans hn
  let _ : NeZero n := ⟨hn'.ne'⟩
  have hl : l ≤ Fintype.card (Fin n) := by simpa using (le_max_left _ _).trans hn
  obtain ⟨P,hP,hlo,hhi,hreg⟩ := szemeredi_regularity J (by positivity : 0 < θ/8) hl
  let B := blockGraph J P θ
  let S := (P.parts ×ˢ P.parts).filter (fun z => block J P θ z.1 z.2)
  let rect := fun z : Finset (Fin n) × Finset (Fin n) => z.1 ×ˢ z.2
  have memS (z : Finset (Fin n) × Finset (Fin n)) : z ∈ S ↔ block J P θ z.1 z.2 := by
    exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨mem_product.mpr ⟨h.1,h.2.1⟩,h⟩⟩
  have rk : S.card ≤ k^2 := by
    calc
      _ ≤ _ := card_le_card (filter_subset _ _)
      _ = P.parts.card^2 := by rw [card_product,sq]
      _ ≤ _ := Nat.pow_le_pow_left hhi 2
  have disj : (S : Set _).PairwiseDisjoint rect := by
    intro a ha b hb hne
    apply Finset.disjoint_left.mpr
    rintro ⟨x,y⟩ hxa hxb
    obtain ⟨hx,hy⟩ := mem_product.mp hxa
    obtain ⟨hx',hy'⟩ := mem_product.mp hxb
    have h₁ := (memS _).mp ha
    have h₂ := (memS _).mp hb
    apply hne
    exact Prod.ext (P.disjoint.elim h₁.1 h₂.1 (not_disjoint_iff.mpr ⟨x,hx,hx'⟩))
      (P.disjoint.elim h₁.2.1 h₂.2.1 (not_disjoint_iff.mpr ⟨y,hy,hy'⟩))
  have hunion : S.biUnion rect = (univ : Finset (Fin n × Fin n)).filter (fun z => B.Adj z.1 z.2) := by
    ext ⟨x,y⟩
    simp only [mem_biUnion,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨z,hz,hxy⟩
      exact ⟨z.1,z.2,(memS z).mp hz,(mem_product.mp hxy).1,(mem_product.mp hxy).2⟩
    · rintro ⟨U,V,h,hx,hy⟩
      exact ⟨(U,V),(memS _).mpr h,mem_product.mpr ⟨hx,hy⟩⟩
  have area : ∑ z ∈ S, z.1.card*z.2.card = 2*B.edgeFinset.card := by
    rw [B.two_mul_card_edgeFinset,← hunion,card_biUnion disj]
    simp [rect]
  have half := mantel B (block_free P hθ ht hJ)
  refine ⟨S,rk,?_,?_⟩
  · have realArea : ∑ z ∈ S, (z.1.card:ℝ)*z.2.card = 2*(B.edgeFinset.card:ℝ) := by exact_mod_cast area
    rw [realArea]
    have hh : 4*(B.edgeFinset.card:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast half
    linarith
  · let R := J.regularityReduced P (θ/8) (θ/4)
    have hcount : 2*R.edgeFinset.card ≤ ∑ z ∈ S, (J.interedges z.1 z.2).card := by
      rw [R.two_mul_card_edgeFinset]
      apply (card_le_card (t:=S.biUnion (fun z => J.interedges z.1 z.2)) ?_).trans card_biUnion_le
      rintro ⟨x,y⟩ hxy
      obtain ⟨hxy,U,hu,V,hv,hx,hy,huv,ruv,duv⟩ := (mem_filter.mp hxy).2
      exact mem_biUnion.mpr ⟨(U,V),(memS _).mpr ⟨hu,hv,huv,ruv,duv⟩,
        (J.mk_mem_interedges_iff).mpr ⟨hx,hy,hxy⟩⟩
    have hpLo : 4/θ ≤ (P.parts.card:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hlo)
    have hdel := SimpleGraph.regularityReduced_edges_card_aux hθ hP hreg hpLo
    change 2*(↑J.edgeFinset.card-↑R.edgeFinset.card : ℝ) < _ at hdel
    simp only [Fintype.card_fin,Nat.cast_pow] at hdel
    have hcount' : 2*(R.edgeFinset.card:ℝ) ≤ ∑ z ∈ S, ((J.interedges z.1 z.2).card:ℝ) := by exact_mod_cast hcount
    have heps : 2*θ ≤ η := by have h := min_le_left (η/2) (1:ℝ); dsimp [θ]; linarith
    nlinarith only [hdel,hcount',mul_le_mul_of_nonneg_right heps (sq_nonneg (n:ℝ))]

end Szemeredi22

open Finset Filter SimpleGraph
open scoped Classical

theorem OMA.solution : type_of% @Erdos22.erdos_22.variants.szemeredi_upper := by
  classical
  intro ε he
  let η := ε/8
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K,hK⟩ := Szemeredi22.rectangle_cover η hη
  let δ := min (triangleRemovalBound η/2) (ε/((K:ℝ)+1))
  have hδ : 0 < δ := lt_min (by have := triangleRemovalBound_pos hη; positivity) (by positivity)
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hK,eventually_ge_atTop 1] with n hcover hn G hG hα
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hsmall : (#(G.cliqueFinset 3) : ℝ) < triangleRemovalBound η * n^3 := by
    have hf : (#(G.cliqueFinset 3) : ℝ) ≤ G.indepNum * (n:ℝ)^2 := by exact_mod_cast Szemeredi22.few_triangles n G hG
    calc
      _ ≤ _ := hf
      _ ≤ (δ*n)*n^2 := by gcongr
      _ = δ*n^3 := by ring
      _ < _ := by
        have hp := triangleRemovalBound_pos hη
        apply mul_lt_mul_of_pos_right _ (by positivity)
        exact (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨J,hJG,inst,hloss,hfree⟩ := G.triangle_removal (by simpa using hsmall)
  have eqD : inst = (fun x y => Classical.propDecidable (J.Adj x y)) := Subsingleton.elim _ _
  subst inst
  have hloss' : (#G.edgeFinset : ℝ) - #J.edgeFinset < η*(n:ℝ)^2 := by
    simpa using hloss
  obtain ⟨S,hs,ha,hj⟩ := hcover J hfree
  have pairs (z : Finset (Fin n) × Finset (Fin n)) :
      2*((J.interedges z.1 z.2).card : ℝ) ≤
        (z.1.card:ℝ)*z.2.card + 3*G.indepNum*n := by
    have sub : J.interedges z.1 z.2 ⊆ G.interedges z.1 z.2 := by
      intro p hp
      obtain ⟨hx,hy,he⟩ := (J.mem_interedges_iff).mp hp
      exact (G.mem_interedges_iff).mpr ⟨hx,hy,hJG he⟩
    exact_mod_cast (Nat.mul_le_mul_left 2 (card_le_card sub)).trans (Szemeredi22.half_cut n G hG _ _)
  have total := sum_le_sum (s:=S) (fun z _ => pairs z)
  rw [← mul_sum,sum_add_distrib] at total
  simp only [sum_const,nsmul_eq_mul] at total
  have hKδ : (K:ℝ)*δ ≤ ε := by
    have h := min_le_right (triangleRemovalBound η/2) (ε/((K:ℝ)+1))
    change δ ≤ _ at h
    have := (le_div_iff₀ (by positivity : 0 < (K:ℝ)+1)).mp h
    linarith
  have herror : (S.card:ℝ)*(3*G.indepNum*n) ≤ 3*ε*n^2 := by
    calc
      _ ≤ (K:ℝ)*(3*(δ*n)*n) := by gcongr
      _ = (K*δ)*(3*(n:ℝ)^2) := by ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hKδ (show 0 ≤ 3*(n:ℝ)^2 by positivity)]
  dsimp [η] at hloss' hj
  nlinarith only [hloss',hj,total,ha,herror,show 0 ≤ ε*(n:ℝ)^2 by positivity]

