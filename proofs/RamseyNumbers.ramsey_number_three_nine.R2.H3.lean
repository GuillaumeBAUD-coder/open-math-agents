import OMAReductions.R_RamseyNumbers_ramsey_number_three_nine_R2
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.FinCases

/-!
# Minimum degree 4 in 21-vertex, 52-edge (3,7)-Ramsey graphs

Proves `OMA.R_RamseyNumbers_ramsey_number_three_nine_R2.H3`: every triangle-free graph on 21
vertices with independence number at most 6 and 52 edges has minimum degree at least 4.

Proof structure:
1. Small Ramsey numbers R(3,2)=3, R(3,3)=6, R(3,4)=9, R(3,5)=14, R(3,6)=18 and the finite
   graph encoding/splitting/dual-packing framework adapted from merged proofs
   `RamseyNumbers.ramsey_number_three_seven` and
   `RamseyNumbers.ramsey_number_three_nine.R1.H2.R1.H2.R1.H1` (crediting @MrSeizy,
   @michielkosters, @Deldor14, @sturdy4days).
2. A vertex w of degree <= 3 must have degree 3 (by R(3,6)=18), leaving a 17-vertex (3,6)-graph
   H on its non-neighborhood B and three neighbor-sets A_1, A_2, A_3 inside B.
3. By R(3,4)=9, |A_1|+|A_2|+|A_3| >= 9; combined with `RamseyDeficiency.removed`, e(H) <= 40.
4. Root splitting at a vertex of H of degree d in {3, 4} reduces H to the 13 canonical bases
   b3_0, b4_0..b4_11. Nine bases satisfy e >= 41 via zero-branching dual certificates; the
   remaining four satisfy e >= 40 (forcing e(H)=40 and |A_1|+|A_2|+|A_3|=9) and a complete
   sorted enumerator classifies all 14 labeled 40-edge extensions.
5. Explicit adjacent-swap relabelings collapse all 14 graphs to two isomorphism representatives,
   each ruled out by a single zero-branching dual packing certificate showing that no three
   independent sets of total size <= 9 satisfy the (3,7) contact condition.

Credit: @ovolee37 (agent: antigravity, model: gemini-4-neon)
-/

namespace OMA.Ramsey37Density

open RamseyNumbers SimpleGraph Finset
lemma degree_lt {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree k) (v : Fin n) : G.degree v < k := by
  by_contra! h
  apply hc.mono h (G.neighborFinset v)
  refine ⟨?_, rfl⟩
  rw [G.coe_neighborFinset, G.isClique_compl]
  exact G.isIndepSet_neighborSet_of_triangleFree hG v

lemma nonneighbors_lt {n k m : ℕ} (hr : IsGraphRamsey m 3 k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hc : Gᶜ.CliqueFree (k + 1)) (v : Fin n) : Gᶜ.degree v < m := by
  classical
  by_contra! h
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin m) (s := Gᶜ.neighborFinset v) (by simpa using h)
  have hv (i : Fin m) : Gᶜ.Adj v (f i) :=
    (Gᶜ.mem_neighborFinset v (f i)).mp (hf ⟨i, rfl⟩)
  let H := G.comap f
  let e : H ↪g G := SimpleGraph.Embedding.comap f G
  let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
  apply hr H
  refine ⟨CliqueFree.comap e.isContained hG, ?_⟩
  intro t ht
  have hs : Gᶜ.IsNClique k (t.map f) := by
    refine ⟨?_, (Finset.card_map _).trans ht.card_eq⟩
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
    exact ec.map_adj_iff.mpr (ht.isClique hi hj (fun he => hxy (congrArg f he)))
  apply hc _ (hs.insert (a := v) ?_)
  intro w hw
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
  exact hv i

lemma three_works : IsGraphRamsey 3 3 2 := by
  classical
  rintro G ⟨hG, hc⟩
  apply hG Finset.univ
  refine ⟨?_, by simp⟩
  intro u _ v _ hne
  by_contra h
  apply hc {u, v}
  refine ⟨?_, Finset.card_pair hne⟩
  intro a ha b hb hab
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  refine ⟨hab, ?_⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab rfl).elim
  · exact h
  · exact fun h' => h h'.symm
  · exact (hab rfl).elim

lemma six_works : IsGraphRamsey 6 3 3 := by
  classical
  rintro G ⟨hG, hc⟩
  have hd := degree_lt G hG hc 0
  have hdc := degree_lt Gᶜ hc (by simpa using hG : Gᶜᶜ.CliqueFree 3) 0
  rw [G.degree_compl, Fintype.card_fin] at hdc
  omega

lemma nine_works : IsGraphRamsey 9 3 4 := by
  classical
  rintro G ⟨hG, hc⟩
  have hdegree (v : Fin 9) : G.degree v = 3 := by
    have hd := degree_lt G hG hc v
    have hdc := nonneighbors_lt six_works G hG hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp [hdegree] at hsum
  omega

lemma fourteen_works : IsGraphRamsey 14 3 5 := by
  classical
  rintro G ⟨hG, hc⟩
  have hd := degree_lt G hG hc 0
  have hdc := nonneighbors_lt nine_works G hG hc 0
  rw [G.degree_compl, Fintype.card_fin] at hdc
  omega

end OMA.Ramsey37Density

section Ramsey36Regular
open SimpleGraph Finset

namespace OMA.RamseyRegular

def mask : Fin 18 → Finset (Fin 18) :=
  ![∅, ∅, ∅, ∅, ∅, ∅, {1}, {2}, {3}, {4}, {1, 3}, {1, 4}, {1, 5},
    {2, 3}, {2, 4}, {2, 5}, {3, 5}, {4, 5}]

private def blocked (i j : Fin 18) : Bool :=
  decide ((1 ≤ i.val ∧ i.val < 6 ∧ 1 ≤ j.val ∧ j.val < 6) ∨
    (1 ≤ i.val ∧ i.val < 6 ∧ 6 ≤ j.val ∧ i ∉ mask j) ∨
    (∃ k : Fin 18, 1 ≤ k.val ∧ k.val < 6 ∧ k ∈ mask i ∧ k ∈ mask j ∧ 6 ≤ i.val ∧ 6 ≤ j.val))

private theorem edge_in_six {V : Type*} (G : SimpleGraph V) (hc : Gᶜ.CliqueFree 6)
    (f : Fin 18 ↪ V) (s : Finset (Fin 18)) (hs : s.card = 6) :
    ∃ i ∈ s, ∃ j ∈ s, i < j ∧ G.Adj (f i) (f j) := by
  classical
  by_contra! hn
  apply hc (s.map f)
  refine ⟨?_, (card_map ..).trans hs⟩
  intro x hx y hy hne
  obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
  obtain ⟨j, hj, rfl⟩ := mem_map.mp hy
  refine ⟨hne, ?_⟩
  rcases lt_or_gt_of_ne (fun h => hne (congrArg f h)) with h | h
  · exact hn i hi j hj h
  · exact fun ha => hn j hj i hi h ha.symm

theorem canonical_impossible {V : Type*} (G : SimpleGraph V)
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) (f : Fin 18 ↪ V)
    (ha : ∀ i j : Fin 18, 1 ≤ i.val → i.val < 6 → 1 ≤ j.val → j.val < 6 →
      ¬ G.Adj (f i) (f j))
    (hab : ∀ i j : Fin 18, 1 ≤ i.val → i.val < 6 → 6 ≤ j.val →
      (G.Adj (f i) (f j) ↔ i ∈ mask j)) : False := by
  classical
  have impossible (i j : Fin 18) (h : blocked i j) : ¬ G.Adj (f i) (f j) := by
    simp only [blocked, decide_eq_true_eq] at h
    rcases h with ⟨hi, hi', hj, hj'⟩ | ⟨hi, hi', hj, hm⟩ | ⟨k, hk, hk', hki, hkj, hi, hj⟩
    · exact ha i j hi hi' hj hj'
    · exact fun hadj => hm ((hab i j hi hi' hj).mp hadj)
    · intro hadj
      exact (G.isIndepSet_neighborSet_of_triangleFree ht (f k))
        ((hab k i hk hk' hi).mpr hki) ((hab k j hk hk' hj).mpr hkj) hadj.ne hadj
  have forced (s : Finset (Fin 18)) (a b : Fin 18) (hs : s.card = 6)
      (only : ∀ i ∈ s, ∀ j ∈ s, i < j → blocked i j ∨ (i = a ∧ j = b)) :
      G.Adj (f a) (f b) := by
    obtain ⟨i, hi, j, hj, hij, he⟩ := edge_in_six G hc f s hs
    rcases only i hi j hj hij with hn | ⟨rfl, rfl⟩
    · exact (impossible i j hn he).elim
    · exact he
  have e78 := forced {1,4,5,7,8,13} 7 8 (by decide +kernel) (by decide +kernel)
  have e79 := forced {1,3,5,7,9,14} 7 9 (by decide +kernel) (by decide +kernel)
  have e716 := forced {1,4,7,13,15,16} 7 16 (by decide +kernel) (by decide +kernel)
  have e717 := forced {1,3,7,14,15,17} 7 17 (by decide +kernel) (by decide +kernel)
  let neighbors : Finset (Fin 18) := {8,9,16,17}
  have adjacent (i : Fin 18) (hi : i ∈ neighbors) : G.Adj (f 7) (f i) := by
    simp only [neighbors, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> assumption
  let six : Finset (Fin 18) := {1,2,8,9,16,17}
  have cases : ∀ i ∈ six, ∀ j ∈ six, i < j → blocked i j ∨
      (i ∈ neighbors ∧ j ∈ neighbors) := by decide +kernel
  obtain ⟨i, hi, j, hj, hij, he⟩ := edge_in_six G hc f six (by decide +kernel)
  rcases cases i hi j hj hij with hn | ⟨hni, hnj⟩
  · exact impossible i j hn he
  · exact (G.isIndepSet_neighborSet_of_triangleFree ht (f 7))
      (adjacent i hni) (adjacent j hnj) he.ne he

end OMA.RamseyRegular

namespace OMA.RamseyRegular

def shape : Fin 15 → Finset (Fin 5) :=
  ![{0}, {1}, {2}, {3}, {4}, {0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}]

def template : Fin 12 → Finset (Fin 5) :=
  ![{0}, {1}, {2}, {3}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 4}, {3, 4}]

def permRow : Fin 15 → Fin 5 → Fin 5 :=
  ![![1, 2, 3, 4, 0],
    ![1, 3, 2, 4, 0],
    ![1, 4, 2, 3, 0],
    ![0, 2, 3, 4, 1],
    ![0, 3, 2, 4, 1],
    ![0, 4, 2, 3, 1],
    ![0, 1, 3, 4, 2],
    ![0, 3, 1, 4, 2],
    ![0, 4, 1, 3, 2],
    ![0, 1, 2, 4, 3],
    ![0, 2, 1, 4, 3],
    ![0, 4, 1, 2, 3],
    ![0, 1, 2, 3, 4],
    ![0, 2, 1, 3, 4],
    ![0, 3, 1, 2, 4]]

def imageIndex : Fin 15 → Fin 12 → Fin 15 :=
  ![![1, 2, 3, 4, 10, 11, 5, 12, 13, 6, 7, 8],
    ![1, 3, 2, 4, 9, 11, 5, 12, 14, 7, 6, 8],
    ![1, 4, 2, 3, 9, 10, 5, 13, 14, 8, 6, 7],
    ![0, 2, 3, 4, 7, 8, 5, 12, 13, 9, 10, 11],
    ![0, 3, 2, 4, 6, 8, 5, 12, 14, 10, 9, 11],
    ![0, 4, 2, 3, 6, 7, 5, 13, 14, 11, 9, 10],
    ![0, 1, 3, 4, 7, 8, 6, 10, 11, 9, 12, 13],
    ![0, 3, 1, 4, 5, 8, 6, 10, 14, 12, 9, 13],
    ![0, 4, 1, 3, 5, 7, 6, 11, 14, 13, 9, 12],
    ![0, 1, 2, 4, 6, 8, 7, 9, 11, 10, 12, 14],
    ![0, 2, 1, 4, 5, 8, 7, 9, 13, 12, 10, 14],
    ![0, 4, 1, 2, 5, 6, 7, 11, 13, 14, 10, 12],
    ![0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 13, 14],
    ![0, 2, 1, 3, 5, 7, 8, 9, 12, 13, 11, 14],
    ![0, 3, 1, 2, 5, 6, 8, 10, 12, 14, 11, 13]]

private theorem row_injective (r : Fin 15) : Function.Injective (permRow r) := by
  exact (show ∀ d i j, permRow d i = permRow d j → i = j by decide +kernel) r

def patternPerm (r : Fin 15) : Fin 5 ↪ Fin 5 :=
  ⟨permRow r, row_injective r⟩

private theorem image_correct : ∀ (r : Fin 15) (j : Fin 12),
    shape (imageIndex r j) = (template j).map (patternPerm r) := by decide +kernel

private def Covers (a b c : Fin 15) : Prop :=
  let T := ({a,b,c} : Finset (Fin 15))ᶜ
  (∀ x : Fin 5, (T.filter (fun i => x ∈ shape i)).card = 4) →
  ∃ r : Fin 15, ∀ t : Fin 12, imageIndex r t ∈ T

private instance (a b c : Fin 15) : Decidable (Covers a b c) := by
  unfold Covers
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem cover : ∀ a b c, Covers a b c := by
  intro a
  fin_cases a <;> decide +kernel

theorem normalize_masks (S : Finset (Fin 15)) (hS : S.card = 12)
    (hrow : ∀ x : Fin 5, (S.filter (fun i => x ∈ shape i)).card = 4) :
    ∃ p : Fin 5 ↪ Fin 5, ∀ j : Fin 12, ∃ k ∈ S, shape k = (template j).map p := by
  have hthree : Sᶜ.card = 3 := by rw [Finset.card_compl, Fintype.card_fin, hS]
  obtain ⟨a,b,c, _, _, _, h⟩ := Finset.card_eq_three.mp hthree
  have hS' : S = ({a,b,c} : Finset (Fin 15))ᶜ := by
    simpa using congrArg (fun s : Finset (Fin 15) => sᶜ) h
  subst S
  obtain ⟨r, hr⟩ := cover a b c hrow
  exact ⟨patternPerm r, fun j => ⟨imageIndex r j, hr j, image_correct r j⟩⟩

end OMA.RamseyRegular

namespace OMA.Ramsey36Canonical


open SimpleGraph

private lemma nonneighbors_five_regular
    (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6)
    (x : Fin 18) (hx : G.degree x = 5)
    (y : Fin 18) (hy : y ∈ Gᶜ.neighborFinset x) :
    (Gᶜ.neighborFinset x ∩ G.neighborFinset y).card ∈ ({3,4} : Finset ℕ) := by
  classical
  have hcard : (Gᶜ.neighborFinset x).card = 12 := by
    rw [Gᶜ.card_neighborFinset_eq_degree, G.degree_compl, Fintype.card_fin, hx]
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 12) (s := Gᶜ.neighborFinset x) (by simp [hcard])
  have hsub_map : Finset.univ.map f ⊆ Gᶜ.neighborFinset x := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
    exact hf ⟨i, rfl⟩
  have hmap : Finset.univ.map f = Gᶜ.neighborFinset x :=
    Finset.eq_of_subset_of_card_le hsub_map (by simp [hcard])
  let H := G.comap f
  let e : H ↪g G := SimpleGraph.Embedding.comap f G
  let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
  have hH : H.CliqueFree 3 := CliqueFree.comap e.isContained hG
  have hHc : Hᶜ.CliqueFree 5 := by
    intro t ht
    have hs : Gᶜ.IsNClique 5 (t.map f) := by
      refine ⟨?_, (Finset.card_map _).trans ht.card_eq⟩
      intro u hu v hv huv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hv
      exact ec.map_adj_iff.mpr (ht.isClique hi hj (fun he => huv (congrArg f he)))
    apply hc _ (hs.insert (a := x) ?_)
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
    exact (Gᶜ.mem_neighborFinset x (f i)).mp (hf ⟨i, rfl⟩)
  have hdeg_all : ∀ i : Fin 12, H.degree i ∈ ({3,4} : Finset ℕ) := by
    intro i
    have hlt := OMA.Ramsey37Density.degree_lt H hH hHc i
    have hnl := OMA.Ramsey37Density.nonneighbors_lt
      OMA.Ramsey37Density.nine_works H hH hHc i
    rw [H.degree_compl, Fintype.card_fin] at hnl
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp (hmap ▸ hy)
  have hinter : Gᶜ.neighborFinset x ∩ G.neighborFinset (f i) = (H.neighborFinset i).map f := by
    ext w
    simp only [← hmap, Finset.mem_inter, Finset.mem_map, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨⟨j, rfl⟩, hadj⟩
      exact ⟨j, hadj, rfl⟩
    · rintro ⟨j, hadj, rfl⟩
      exact ⟨⟨j, rfl⟩, hadj⟩
  rw [hinter, Finset.card_map, H.card_neighborFinset_eq_degree]
  exact hdeg_all i

theorem mask_arity (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) (hdeg : ∀ x, G.degree x = 5)
    (v u : Fin 18) (hu : u ∈ Gᶜ.neighborFinset v) :
    (G.neighborFinset v ∩ G.neighborFinset u).card ∈ ({1,2} : Finset ℕ) := by
  have hv := hdeg v
  let A := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  have hAB_disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    rw [G.mem_neighborFinset] at hwA
    rw [Gᶜ.mem_neighborFinset] at hwB
    exact hwB.2 hwA
  have hA_deg_u : ∀ u ∈ B, (A ∩ G.neighborFinset u).card ∈ ({1,2} : Finset ℕ) := by
    intro u hu
    have hB_reg := nonneighbors_five_regular G hG hc v hv u hu
    have hsub : G.neighborFinset u ⊆ A ∪ B := by
      intro w hw
      rw [G.mem_neighborFinset] at hw
      have hvw : v ≠ w := by
        rintro rfl
        exact ((Gᶜ.mem_neighborFinset v u).mp hu).2 hw.symm
      by_cases hvw_adj : G.Adj v w
      · exact Finset.mem_union_left _ ((G.mem_neighborFinset v w).mpr hvw_adj)
      · exact Finset.mem_union_right _ ((Gᶜ.mem_neighborFinset v w).mpr ⟨hvw, hvw_adj⟩)
    have hsplit : G.neighborFinset u = (A ∩ G.neighborFinset u) ∪ (B ∩ G.neighborFinset u) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hw
        rcases Finset.mem_union.mp (hsub hw) with hA | hB
        · exact Or.inl ⟨hA, hw⟩
        · exact Or.inr ⟨hB, hw⟩
      · rintro (⟨_, hw⟩ | ⟨_, hw⟩) <;> exact hw
    have hdisj_u : Disjoint (A ∩ G.neighborFinset u) (B ∩ G.neighborFinset u) :=
      hAB_disj.mono Finset.inter_subset_left Finset.inter_subset_left
    have hdeg_u : G.degree u = (A ∩ G.neighborFinset u).card + (B ∩ G.neighborFinset u).card := by
      conv_lhs => rw [← G.card_neighborFinset_eq_degree, hsplit, Finset.card_union_of_disjoint hdisj_u]
    change (B ∩ G.neighborFinset u).card ∈ ({3,4} : Finset ℕ) at hB_reg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB_reg ⊢
    have := hdeg u
    omega
  exact hA_deg_u u hu

private theorem shared_neighbor_forbids (G : SimpleGraph (Fin 18))
    (hG : G.CliqueFree 3) {a x y : Fin 18} (hx : G.Adj a x) (hy : G.Adj a y) :
    ¬ G.Adj x y := fun h =>
  G.isIndepSet_neighborSet_of_triangleFree hG a hx hy (G.ne_of_adj h) h

theorem row_degree (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hdeg : ∀ x, G.degree x = 5)
    {v a : Fin 18} (ha : a ∈ G.neighborFinset v) :
    (Gᶜ.neighborFinset v ∩ G.neighborFinset a).card = 4 := by
  have hva := (G.mem_neighborFinset v a).mp ha
  have hv_mem : v ∈ G.neighborFinset a := (G.mem_neighborFinset _ _).mpr hva.symm
  have heq : Gᶜ.neighborFinset v ∩ G.neighborFinset a = (G.neighborFinset a).erase v := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_erase, Gᶜ.mem_neighborFinset, G.mem_neighborFinset]
    constructor
    · rintro ⟨⟨hvw, _⟩, haw⟩
      exact ⟨hvw.symm, haw⟩
    · rintro ⟨hwv, haw⟩
      exact ⟨⟨hwv.symm, shared_neighbor_forbids G hG hva.symm haw⟩, haw⟩
  rw [heq, Finset.card_erase_of_mem hv_mem, G.card_neighborFinset_eq_degree, hdeg]

theorem distinct_masks (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) (hdeg : ∀ x, G.degree x = 5)
    (v : Fin 18) :
    Set.InjOn (fun u => G.neighborFinset v ∩ G.neighborFinset u) (Gᶜ.neighborFinset v) := by
  intro x hx y hy heq
  by_contra hxy
  let A := G.neighborFinset v
  let mask := fun u => A ∩ G.neighborFinset u
  change mask x = mask y at heq
  have hx' := (Gᶜ.mem_neighborFinset v x).mp hx
  have hy' := (Gᶜ.mem_neighborFinset v y).mp hy
  have hadj {u z : Fin 18} (h : z ∈ mask u) : G.Adj u z :=
    (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp h).2
  have hA {u z : Fin 18} (h : z ∈ mask u) : G.Adj v z :=
    (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp h).1
  have hcard := mask_arity G hG hc hdeg v x hx
  change (mask x).card ∈ ({1,2} : Finset ℕ) at hcard
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcard
  rcases hcard with h1 | h2
  · obtain ⟨a, hmask⟩ := Finset.card_eq_one.mp h1
    have ham : a ∈ mask x := by simp [hmask]
    have hya : a ∈ mask y := heq ▸ ham
    have hsub : Gᶜ.IsNClique 4 (A.erase a) := by
      refine ⟨?_, ?_⟩
      · intro i hi j hj hij
        exact ⟨hij, shared_neighbor_forbids G hG
          ((G.mem_neighborFinset _ _).mp (Finset.mem_of_mem_erase hi))
          ((G.mem_neighborFinset _ _).mp (Finset.mem_of_mem_erase hj))⟩
      · have ha : a ∈ A := Finset.mem_inter.mp ham |>.1
        rw [Finset.card_erase_of_mem ha]
        change (G.neighborFinset v).card - 1 = 4
        rw [G.card_neighborFinset_eq_degree, hdeg]
    have join {u : Fin 18} (hu : u ∈ Gᶜ.neighborFinset v) (hm : mask u = {a}) :
        ∀ w ∈ A.erase a, Gᶜ.Adj u w := by
      intro w hw
      have hwA := Finset.mem_of_mem_erase hw
      have hnot := ((Gᶜ.mem_neighborFinset v u).mp hu).2
      refine ⟨?_, ?_⟩
      · intro he
        exact hnot (he ▸ (G.mem_neighborFinset v w).mp hwA)
      · intro huw
        have hwM : w ∈ mask u := Finset.mem_inter.mpr ⟨hwA,(G.mem_neighborFinset _ _).mpr huw⟩
        exact (Finset.ne_of_mem_erase hw) (Finset.mem_singleton.mp (hm ▸ hwM))
    have hxjoin := hsub.insert (join hx hmask)
    apply hc _ (hxjoin.insert (a := y) ?_)
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact ⟨fun h => hxy h.symm, shared_neighbor_forbids G hG (hadj hya).symm (hadj ham).symm⟩
    · exact join hy (heq.symm.trans hmask) w hw
  · obtain ⟨a,b,hab,hm⟩ := Finset.card_eq_two.mp h2
    have hax : a ∈ mask x := by simp [hm]
    have hbx : b ∈ mask x := by simp [hm]
    have hay : a ∈ mask y := heq ▸ hax
    have hby : b ∈ mask y := heq ▸ hbx
    have hcompl : b ∈ Gᶜ.neighborFinset a :=
      (Gᶜ.mem_neighborFinset _ _).mpr ⟨hab, shared_neighbor_forbids G hG (hA hax) (hA hbx)⟩
    have htwo := mask_arity G hG hc hdeg a b hcompl
    simp only [Finset.mem_insert,Finset.mem_singleton] at htwo
    have hmem {z : Fin 18} (haz : G.Adj z a) (hbz : G.Adj z b) :
        z ∈ G.neighborFinset a ∩ G.neighborFinset b :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr haz.symm,
        (G.mem_neighborFinset _ _).mpr hbz.symm⟩
    have hsub : ({v,x,y} : Finset (Fin 18)) ⊆ G.neighborFinset a ∩ G.neighborFinset b := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hmem (hA hax) (hA hbx)
      · exact hmem (hadj hax) (hadj hbx)
      · exact hmem (hadj hay) (hadj hby)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_triple_eq_three_iff.mpr ⟨hx'.1,hy'.1,hxy⟩] at hle
    omega

private theorem enumerateVertices {n : ℕ} (s : Finset (Fin 18)) (hn : s.card = n) :
    ∃ e : Fin n ↪ Fin 18, (∀ i, e i ∈ s) ∧ (∀ z ∈ s, ∃ i, e i = z) := by
  classical
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin n) (s := s) (by simp [hn])
  have hin (i) : e i ∈ s := he ⟨i,rfl⟩
  have hsub : Finset.univ.map e ⊆ s := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
    exact hin i
  have hmap := Finset.eq_of_subset_of_card_le hsub (by simp [hn])
  refine ⟨e, hin, fun z hz => ?_⟩
  obtain ⟨i,_,hi⟩ := Finset.mem_map.mp (hmap ▸ hz)
  exact ⟨i,hi⟩

theorem canonical_parts
    (shape : Fin 15 → Finset (Fin 5)) (template : Fin 12 → Finset (Fin 5))
    (shape_full : ∀ t : Finset (Fin 5), t.card ∈ ({1,2} : Finset ℕ) → ∃ k, shape k = t)
    (template_inj : Function.Injective template)
    (normalize : ∀ S : Finset (Fin 15), S.card = 12 →
      (∀ a : Fin 5, (S.filter (fun i => a ∈ shape i)).card = 4) →
      ∃ p : Fin 5 ↪ Fin 5, ∀ j : Fin 12, ∃ k ∈ S, shape k = (template j).map p)
    (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hc : Gᶜ.CliqueFree 6) (hdeg : ∀ x, G.degree x = 5) (v : Fin 18) :
    ∃ r : Fin 5 ↪ Fin 18, ∃ s : Fin 12 ↪ Fin 18,
      (∀ i, r i ∈ G.neighborFinset v) ∧ (∀ j, s j ∈ Gᶜ.neighborFinset v) ∧
      (∀ i j, G.Adj (r i) (s j) ↔ i ∈ template j) := by
  classical
  let A := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  have hAc : A.card = 5 := (G.card_neighborFinset_eq_degree v).trans (hdeg v)
  have hBc : B.card = 12 := by
    rw [Gᶜ.card_neighborFinset_eq_degree, G.degree_compl, Fintype.card_fin, hdeg]
  obtain ⟨f,hf,fcover⟩ := enumerateVertices A hAc
  obtain ⟨g,hg,gcover⟩ := enumerateVertices B hBc
  let m (j : Fin 12) := Finset.univ.filter fun i => G.Adj (f i) (g j)
  have mem_m (i : Fin 5) (j : Fin 12) : i ∈ m j ↔ G.Adj (f i) (g j) := by simp [m]
  have map_m (j : Fin 12) : (m j).map f = A ∩ G.neighborFinset (g j) := by
    ext z
    constructor
    · intro hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hz
      exact Finset.mem_inter.mpr ⟨hf a,(G.mem_neighborFinset _ _).mpr ((mem_m _ _).mp ha).symm⟩
    · intro hz
      obtain ⟨ha,hadj⟩ := Finset.mem_inter.mp hz
      obtain ⟨a,rfl⟩ := fcover _ ha
      exact Finset.mem_map.mpr ⟨a,(mem_m _ _).mpr ((G.mem_neighborFinset _ _).mp hadj).symm,rfl⟩
  have size_m (j : Fin 12) : (m j).card ∈ ({1,2} : Finset ℕ) := by
    have h := mask_arity G hG hc hdeg v (g j) (hg j)
    change (A ∩ G.neighborFinset (g j)).card ∈ ({1,2} : Finset ℕ) at h
    rwa [← map_m, Finset.card_map] at h
  choose code code_spec using fun j => shape_full (m j) (size_m j)
  have cinj : Function.Injective code := by
    intro i j hij
    have hm : m i = m j := (code_spec i).symm.trans ((congrArg shape hij).trans (code_spec j))
    apply g.injective
    apply distinct_masks G hG hc hdeg v (hg i) (hg j)
    change A ∩ G.neighborFinset (g i) = A ∩ G.neighborFinset (g j)
    rw [← map_m, ← map_m, hm]
  let S := Finset.univ.image code
  have size_S : S.card = 12 := by simp [S, Finset.card_image_of_injective _ cinj]
  have rows (a : Fin 5) : (S.filter (fun i => a ∈ shape i)).card = 4 := by
    let T := Finset.univ.filter fun j => G.Adj (f a) (g j)
    have hinT (j : Fin 12) : j ∈ T ↔ G.Adj (f a) (g j) := by simp [T]
    have hfilter : S.filter (fun i => a ∈ shape i) = T.image code := by
      ext z
      constructor
      · intro hz
        obtain ⟨hz,ha⟩ := Finset.mem_filter.mp hz
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hz
        rw [code_spec] at ha
        exact Finset.mem_image.mpr ⟨j,(hinT j).mpr ((mem_m _ _).mp ha),rfl⟩
      · intro hz
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
        refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,?_⟩
        rw [code_spec]
        exact (mem_m _ _).mpr ((hinT _).mp hj)
    have Tmap : T.map g = B ∩ G.neighborFinset (f a) := by
      ext z
      constructor
      · intro hz
        obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hz
        exact Finset.mem_inter.mpr ⟨hg j,(G.mem_neighborFinset _ _).mpr ((hinT _).mp hj)⟩
      · intro hz
        obtain ⟨hz,hz'⟩ := Finset.mem_inter.mp hz
        obtain ⟨j,rfl⟩ := gcover _ hz
        exact Finset.mem_map.mpr ⟨j,(hinT _).mpr ((G.mem_neighborFinset _ _).mp hz'),rfl⟩
    rw [hfilter, Finset.card_image_of_injective _ cinj, ← Finset.card_map g, Tmap]
    exact row_degree G hG hdeg (hf a)
  obtain ⟨p,hp⟩ := normalize S size_S rows
  have realize (i : Fin 12) : ∃ j, m j = (template i).map p := by
    obtain ⟨k,hk,hshape⟩ := hp i
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hk
    exact ⟨j,(code_spec j).symm.trans hshape⟩
  choose sel hsel using realize
  have sel_inj : Function.Injective sel := by
    intro i j heq
    apply template_inj
    apply Finset.map_injective p
    rw [← hsel, ← hsel, heq]
  let e : Fin 12 ↪ Fin 12 := ⟨sel,sel_inj⟩
  refine ⟨p.trans f,e.trans g,fun i => hf (p i),fun j => hg (sel j),?_⟩
  intro i j
  change G.Adj (f (p i)) (g (sel j)) ↔ i ∈ template j
  rw [← mem_m, hsel]
  exact Finset.mem_map' p


private def joinVertices {V : Type*} (v : V) (r : Fin 5 ↪ V) (s : Fin 12 ↪ V)
    (i : Fin 18) : V :=
  if i.val = 0 then v else if h : i.val < 6 then r ⟨i.val-1, by omega⟩
  else s ⟨i.val-6, by omega⟩

private theorem join_injective {V : Type*} (v : V) (r : Fin 5 ↪ V) (s : Fin 12 ↪ V)
    (hvr : ∀ i, v ≠ r i) (hvs : ∀ j, v ≠ s j) (hrs : ∀ i j, r i ≠ s j) :
    Function.Injective (joinVertices v r s) := by
  intro i j hh
  apply Fin.ext
  unfold joinVertices at hh
  split_ifs at hh
  all_goals first
    | omega
    | exact False.elim (hvr _ hh)
    | exact False.elim (hvr _ hh.symm)
    | exact False.elim (hvs _ hh)
    | exact False.elim (hvs _ hh.symm)
    | exact False.elim (hrs _ _ hh)
    | exact False.elim (hrs _ _ hh.symm)
    | have e := congrArg Fin.val (r.injective hh); dsimp at e; omega
    | have e := congrArg Fin.val (s.injective hh); dsimp at e; omega

private def rowTag (i : Fin 5) : Fin 18 := ⟨i.val+1, by omega⟩
private def colTag (j : Fin 12) : Fin 18 := ⟨j.val+6, by omega⟩
open OMA.RamseyRegular

private theorem template_agrees : ∀ (i : Fin 5) (j : Fin 12),
    i ∈ template j ↔ rowTag i ∈ mask (colTag j) := by decide +kernel

private theorem shapes_complete : ∀ t : Finset (Fin 5),
    t.card ∈ ({1,2} : Finset ℕ) → ∃ k, shape k = t := by decide +kernel

private theorem template_injective : Function.Injective template := by
  intro i j
  exact (show ∀ i j : Fin 12, template i = template j → i = j by decide +kernel) i j

theorem regular_impossible (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hdeg : ∀ x, G.degree x = 5) (hc : Gᶜ.CliqueFree 6) : False := by
  classical
  let v : Fin 18 := 0
  obtain ⟨r,s,hr,hs,hadj⟩ := canonical_parts shape template shapes_complete template_injective normalize_masks G hG hc hdeg v
  have ra (i : Fin 5) : G.Adj v (r i) := (G.mem_neighborFinset _ _).mp (hr i)
  have sb (j : Fin 12) : Gᶜ.Adj v (s j) := (Gᶜ.mem_neighborFinset _ _).mp (hs j)
  have sep (i : Fin 5) (j : Fin 12) : r i ≠ s j := by
    intro he
    exact (sb j).2 (he ▸ ra i)
  let f : Fin 18 ↪ Fin 18 :=
    ⟨joinVertices v r s, join_injective v r s (fun i => (ra i).ne) (fun j => (sb j).1) sep⟩
  have row (i : Fin 18) (hl : 1 ≤ i.val) (hu : i.val < 6) :
      f i = r ⟨i.val-1, by omega⟩ := by
    have h0 : i.val ≠ 0 := by omega
    simp [f, joinVertices, h0, hu]
  have col (j : Fin 18) (hl : 6 ≤ j.val) :
      f j = s ⟨j.val-6, by omega⟩ := by
    have h0 : j.val ≠ 0 := by omega
    have h1 : ¬j.val < 6 := by omega
    simp [f, joinVertices, h0, h1]
  apply canonical_impossible G hG hc f
  · intro i j hil hiu hjl hju
    rw [row i hil hiu, row j hjl hju]
    exact shared_neighbor_forbids G hG (ra _) (ra _)
  · intro i j hil hiu hj
    let a : Fin 5 := ⟨i.val-1,by omega⟩
    let b : Fin 12 := ⟨j.val-6,by omega⟩
    have ai : rowTag a = i := Fin.ext (by dsimp [rowTag,a]; omega)
    have bj : colTag b = j := Fin.ext (by dsimp [colTag,b]; omega)
    rw [row i hil hiu, col j hj]
    exact (hadj a b).trans (by simpa only [ai,bj] using template_agrees a b)


end OMA.Ramsey36Canonical
end Ramsey36Regular

section RamseyFiniteSection
open SimpleGraph
namespace OMA.RamseyFinite

private def bits : List Bool → Nat
  | [] => 0
  | b::bs => 2 * bits bs + b.toNat

private theorem bits_lt (b : List Bool) : bits b < 2 ^ b.length := by
  induction b with
  | nil => decide
  | cons a l ih => cases a <;> simp [bits, pow_succ] <;> omega

private theorem bits_append (a b : List Bool) : bits (a ++ b) = bits a + 2 ^ a.length * bits b := by
  induction a with
  | nil => simp [bits]
  | cons c a ih => simp [bits, ih, pow_succ]; ring

private theorem bits_replicate_false (n : Nat) : bits (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bits, ih]

private theorem bits_replicate_true (n : Nat) : bits (List.replicate n true) + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bits, pow_succ]; omega

private def encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] : List V → List Nat
  | [] => []
  | v::vs => bits (vs.map fun x => decide (G.Adj v x)) :: encode G vs

private def shifted : List Nat → List Nat
  | [] => []
  | s::ss => 2 ^ ss.length * s :: shifted ss

private def attach (blocks base : List Nat) : List Nat :=
  (2 ^ blocks.length - 1) :: (shifted blocks ++ base)

private theorem contacts {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (front base : List V) (hi : ∀ x ∈ front, ∀ y ∈ front, ¬ G.Adj x y) :
    encode G (front ++ base) =
      shifted (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) ++ encode G base := by
  induction front with
  | nil => rfl
  | cons a as ih =>
    have nh (x) (hx : x∈as) := hi a (by simp) x (by simp [hx])
    have nils : as.map (fun x => decide (G.Adj a x)) = List.replicate as.length false := by
      apply List.eq_replicate_iff.mpr
      exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [nh b hb]⟩
    simp [encode, shifted, bits_append, nils, bits_replicate_false,
      ih (fun x hx y hy => hi x (by simp [hx]) y (by simp [hy]))]

private theorem root_encoding {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (front base : List V) (hfront : ∀ x∈front, G.Adj r x)
    (hbase : ∀ x∈base, ¬ G.Adj r x) (ht : G.CliqueFree 3) :
    encode G (r::front++base) = attach
      (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) (encode G base) := by
  have hf : front.map (fun x => decide (G.Adj r x)) = List.replicate front.length true := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [hfront b hb]⟩
  have hb : base.map (fun x => decide (G.Adj r x)) = List.replicate base.length false := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [hbase b hb]⟩
  have hi (x) (hx : x ∈ front) (y) (hy : y ∈ front) (h : G.Adj x y) : False :=
    G.isIndepSet_neighborSet_of_triangleFree ht r (hfront x hx) (hfront y hy) h.ne h
  simp [encode, attach, bits_append, hf, hb, bits_replicate_false, contacts G front base hi]
  have := bits_replicate_true front.length
  omega

private def mark {V : Type*} [DecidableEq V] (vs : List V) (s : Finset V) : Nat :=
  bits (vs.map fun x => decide (x ∈ s))

private theorem bit_form (b : Bool) (n : Nat) : Nat.bit b n = 2 * n + b.toNat := by
  cases b <;> simp [Nat.bit, Nat.two_mul]

private theorem and_mask {V : Type*} (vs : List V) (f g : V → Bool) :
    bits (vs.map f) &&& bits (vs.map g) = 0 ↔ ∀ x ∈ vs, f x = true → g x = false := by
  induction vs with
  | nil => simp [bits]
  | cons a l ih =>
    simp only [List.map_cons, bits, ← bit_form, Nat.land_bit, List.forall_mem_cons]
    rw [bit_form]
    cases f a <;> cases g a <;> simp [ih]

private def ind0 (p : Nat × Nat) : Nat × Nat := (2*p.1,p.2)
private def ind1 (p : Nat × Nat) : Nat × Nat := (2*p.1+1,p.2+1)

private def inds : List Nat → List (Nat × Nat)
  | [] => [(0,0)]
  | m::rows =>
    let t := inds rows
    t.map ind0 ++ (t.filter fun p => m &&& p.1 == 0).map ind1

private theorem mark_congr {V : Type*} [DecidableEq V] (vs : List V) (s t : Finset V)
    (h : ∀ x∈vs, x∈s ↔ x∈t) : mark vs s = mark vs t := by
  unfold mark
  congr 1
  exact List.map_congr_left (fun x hx => by simp only [h x hx])

private theorem inds_sound {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (hn : vs.Nodup) {p : Nat × Nat} (hp : p ∈ inds (encode G vs)) :
    ∃ S : Finset V, S ⊆ vs.toFinset ∧ Gᶜ.IsClique (S : Set V) ∧ p = (mark vs S,S.card) := by
  induction vs generalizing p with
  | nil =>
    simp [encode,inds] at hp
    exact ⟨∅,by simp,by simp,by simp [hp,mark,bits]⟩
  | cons a l ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [encode,inds,List.mem_append,List.mem_map,List.mem_filter] at hp
    rcases hp with ⟨q,hq,rfl⟩ | ⟨q,⟨hq,hd⟩,rfl⟩
    · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
      have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
      exact ⟨S,by simpa using hS.trans (Finset.subset_insert a _),hI,by simp [ind0,mark,bits,ha]⟩
    · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
      have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
      have hz := (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈S))).mp (beq_iff_eq.mp hd)
      have hi : Gᶜ.IsClique (insert a S : Finset V) := by
        rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem ha]
        refine ⟨hI,fun x hx => ⟨?_,?_⟩⟩
        · exact fun e => ha (e ▸ hx)
        · intro adj
          have := hz x (List.mem_toFinset.mp (hS hx)) (by simpa using adj)
          exact (of_decide_eq_false this) hx
      have hm := mark_congr l (insert a S) S (by intro x hx; simp [show x ≠ a from fun e => hn'.1 (e ▸ hx)])
      refine ⟨insert a S, by simpa using Finset.insert_subset_insert a hS, hi, ?_⟩
      simp [ind1,mark,bits,Finset.card_insert_of_notMem ha] at hm ⊢
      omega

private theorem inds_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (hn : vs.Nodup) (S : Finset V) (hS : S ⊆ vs.toFinset) (hI : Gᶜ.IsClique (S : Set V)) :
    (mark vs S,S.card) ∈ inds (encode G vs) := by
  induction vs generalizing S with
  | nil =>
    have e : S=∅ := Finset.subset_empty.mp (by simpa using hS)
    simp [e,encode,inds,mark,bits]
  | cons a l ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [encode,inds,List.mem_append,List.mem_map,List.mem_filter]
    by_cases ha : a ∈ S
    · let T := S.erase a
      have hT : T ⊆ l.toFinset := by
        intro x hx
        have m := Finset.mem_erase.mp hx
        have h := List.mem_cons.mp (List.mem_toFinset.mp (hS m.2))
        exact List.mem_toFinset.mpr (h.resolve_left m.1)
      have hI' := hI.subset (show (T : Set V) ⊆ (S : Set V) from Finset.erase_subset ..)
      have hmark := mark_congr l S T (by intro x hx; simp [T,show x≠a from fun e => hn'.1 (e ▸ hx)])
      have hcard : T.card + 1 = S.card := Finset.card_erase_add_one ha
      right
      refine ⟨(mark l T,T.card),⟨ih hn'.2 T hT hI', ?_⟩,?_⟩
      · apply beq_iff_eq.mpr
        apply (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈T))).mpr
        intro x _ hx
        apply decide_eq_false
        intro hm
        have hmem := Finset.mem_erase.mp hm
        exact (hI ha hmem.2 hmem.1.symm).2 (of_decide_eq_true hx)
      · simp [ind1,mark,bits,ha,hcard] at hmark ⊢
        omega
    · have hT : S ⊆ l.toFinset := by
        intro x hx
        have h := List.mem_cons.mp (List.mem_toFinset.mp (hS hx))
        exact List.mem_toFinset.mpr (h.resolve_left (fun e => ha (e ▸ hx)))
      exact Or.inl ⟨_,ih hn'.2 S hT hI,by simp [ind0,mark,bits,ha]⟩


private def countBits : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,x => (x%2) + countBits n (x/2)

private def bump (m : Nat) : List Nat → List Nat
  | [] => []
  | x::xs => (x+m%2)::bump (m/2) xs

private def degrees : List Nat → List Nat
  | [] => []
  | m::ms => countBits ms.length m :: bump m (degrees ms)

private def sizeAt {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) (x : V) :=
  (vs.filter fun y => decide (G.Adj x y)).length

private theorem half_step (x : Nat) : (2*x+1)/2=x := by omega

private theorem count_map {V : Type*} (vs : List V) (f : V → Bool) :
    countBits vs.length (bits (vs.map f)) = (vs.filter f).length := by
  induction vs with
  | nil => rfl
  | cons a l ih =>
    cases ha : f a <;> simp [countBits,bits,ha,ih,half_step]
    omega

private theorem bump_map {V : Type*} (vs : List V) (f : V → Bool) (d : V → Nat) :
    bump (bits (vs.map f)) (vs.map d) = vs.map (fun x => d x + (f x).toNat) := by
  induction vs with
  | nil => rfl
  | cons a l ih => cases ha : f a <;> simp [bump,bits,ha,ih,half_step]

private theorem encode_length {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) :
    (encode G vs).length=vs.length := by induction vs with | nil => rfl | cons a as ih => simp [encode,ih]

private theorem degrees_encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) :
    degrees (encode G vs) = vs.map (sizeAt G vs) := by
  induction vs with
  | nil => rfl
  | cons a l ih =>
    simp only [encode,degrees,encode_length,count_map,ih,bump_map,List.map_cons,List.cons.injEq]
    refine ⟨by simp [sizeAt], List.map_congr_left ?_⟩
    intro x _
    by_cases h : G.Adj a x <;> simp [sizeAt,h,G.adj_comm x a]

private theorem sizeAt_finset {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {vs : List V} (hn : vs.Nodup) (x : V) :
    sizeAt G vs x = (vs.toFinset.filter (G.Adj x)).card := by
  have h := List.toFinset_filter vs (fun y => decide (G.Adj x y))
  simp only [decide_eq_true_eq] at h
  rw [← h, List.toFinset_card_of_nodup (hn.filter _)]
  rfl


private def Small {V : Type*} (G : SimpleGraph V) (A : Finset V) (k : Nat) :=
  ∀ I ⊆ A, Gᶜ.IsClique (I : Set V) → I.card < k

private theorem row_mark {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (base : List V) (x : V) :
    bits (base.map fun y => decide (G.Adj x y)) = mark base (base.toFinset.filter (G.Adj x)) := by
  unfold mark
  congr 1
  exact List.map_congr_left (fun y hy => by simp [hy])

private theorem neighbors_small {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (A : Finset V) (x : V) :
    Gᶜ.IsClique ((A.filter (G.Adj x) : Finset V) : Set V) := by
  rw [G.isClique_compl]
  intro y hy z hz hn
  exact G.isIndepSet_neighborSet_of_triangleFree ht x (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2 hn

private theorem degrees_bound {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (A : Finset V) (k : Nat) (hs : Small G A k)
    (l : List V) (hn : l.Nodup) (hsub : l.toFinset ⊆ A) :
    (degrees (encode G l)).all (· < k) = true := by
  rw [degrees_encode, List.all_eq_true]
  intro y hy
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hy
  simp only [decide_eq_true_eq, sizeAt_finset G hn]
  exact hs _ ((Finset.filter_subset _ _).trans hsub) (neighbors_small G ht _ x)

private def okContacts (k : Nat) (isets : List (Nat × Nat)) (cs : List Nat) : Bool :=
  isets.all fun p => p.2 + (cs.filter fun v => v &&& p.1 == 0).length < k

private theorem ok_contacts {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : Nat) (hs : Small G A k) (front base : List V)
    (hn : (front++base).Nodup) (hsub : (front++base).toFinset ⊆ A)
    (hi : Gᶜ.IsClique (front.toFinset : Set V)) :
    okContacts k (inds (encode G base)) (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) := by
  rw [okContacts,List.all_eq_true]
  intro q hq
  obtain ⟨hh,hb,hd⟩ := List.nodup_append.mp hn
  obtain ⟨S,hS,hI,rfl⟩ := inds_sound G base hb hq
  let pred (v : V) : Bool := bits (base.map fun y => decide (G.Adj v y)) &&& mark base S == 0
  let F := front.filter pred
  have hF (x) (hx : x∈F) : x∈front := (List.mem_filter.mp hx).1
  have sep (x) (hx : x∈F) (y) (hy : y∈S) : Gᶜ.Adj x y := by
    have hx' := List.mem_filter.mp hx
    have hy' := List.mem_toFinset.mp (hS hy)
    have neq : x ≠ y := hd x hx'.1 y hy'
    exact ⟨neq,fun ha => by
      have e := (and_mask base (fun z => decide (G.Adj x z)) (fun z => decide (z ∈ S))).mp
        (beq_iff_eq.mp hx'.2) y hy' (by simpa using ha)
      exact of_decide_eq_false e hy⟩
  have sub : F.toFinset ∪ S ⊆ A := by
    apply Finset.union_subset
    · exact fun x hx => hsub (by simp [hF x (List.mem_toFinset.mp hx)])
    · exact fun x hx => hsub (by simp [List.mem_toFinset.mp (hS hx)])
  have together : Gᶜ.IsClique ((F.toFinset ∪ S : Finset V) : Set V) := by
    rw [Finset.coe_union, SimpleGraph.IsClique, Set.pairwise_union]
    refine ⟨hi.subset ?_,hI,?_⟩
    · exact fun x hx => List.mem_toFinset.mpr (hF x (List.mem_toFinset.mp hx))
    · intro x hx y hy _
      exact ⟨sep x (List.mem_toFinset.mp hx) y hy,(sep x (List.mem_toFinset.mp hx) y hy).symm⟩
  have dis : Disjoint F.toFinset S := Finset.disjoint_left.mpr fun x hx hy =>
    (sep x (List.mem_toFinset.mp hx) x hy).ne rfl
  have w := hs _ sub together
  rw [Finset.card_union_of_disjoint dis,List.toFinset_card_of_nodup (hh.filter _)] at w
  simp only [decide_eq_true_eq,List.filter_map,List.length_map]
  change S.card + F.length < k
  simpa only [F, Nat.add_comm S.card] using w


private theorem bit_and {α : Type*} (l : List α) (f g : α → Bool) :
    bits (l.map f) &&& bits (l.map g) = bits (l.map fun x => f x && g x) := by
  induction l with
  | nil => simp [bits]
  | cons a l ih => simp only [List.map_cons,bits,← bit_form,Nat.land_bit,ih]

private theorem bit_or {α : Type*} (l : List α) (f g : α → Bool) :
    bits (l.map f) ||| bits (l.map g) = bits (l.map fun x => f x || g x) := by
  induction l with
  | nil => simp [bits]
  | cons a l ih => simp only [List.map_cons,bits,← bit_form,Nat.lor_bit,ih]

private def compat (I : List (Nat × Nat)) (a : Nat) := bits (I.map fun p => a &&& p.1 == 0)
private def universal (I : List (Nat × Nat)) := bits (I.map fun _=>true)
private def threshold (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (j : Nat) :=
  bits (I.map fun p => decide (k≤p.2 + (acc.filter fun a => a &&& p.1 == 0).length+j))

private theorem saturated (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (j : Nat) (h : k≤j) :
    threshold k I acc j=universal I := by
  unfold threshold universal
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [decide_eq_true_eq]; omega

private theorem threshold_cons (k : Nat) (I : List (Nat × Nat)) (a : Nat) (acc : List Nat) (j : Nat) :
    threshold k I (a::acc) j = threshold k I acc j ||| (compat I a &&& threshold k I acc (j+1)) := by
  unfold threshold compat
  rw [bit_and,bit_or]
  congr 1
  apply List.map_congr_left
  intro p _
  apply Bool.eq_iff_iff.mpr
  by_cases e : a &&& p.1=0 <;> simp [e] <;> omega

private def cells (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,j => threshold k I acc j :: cells k I acc n (j+1)

private def tick (u m : Nat) : List Nat → List Nat
  | [] => []
  | a::as => (a ||| (m &&& as.headD u)) :: tick u m as

private theorem tick_cells (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (a n j : Nat) (h : k ≤ j+n) :
    tick (universal I) (compat I a) (cells k I acc n j) = cells k I (a::acc) n j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [cells,tick,List.cons.injEq]
    refine ⟨?_,ih (j+1) (by omega)⟩
    rw [threshold_cons]
    cases n with
    | zero => simp [cells,saturated k I acc (j+1) (by omega)]
    | succ n => rfl

private theorem can_add (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (a : Nat)
    (h : okContacts k I (a::acc)) : compat I a &&& threshold k I acc 1=0 := by
  apply (and_mask I _ _).mpr
  intro p hp e
  have b := List.all_eq_true.mp h p hp
  simp only [List.filter_cons,e,if_true,List.length_cons,decide_eq_true_eq] at b
  apply decide_eq_false
  omega

private def traverse (opts : List (Nat × Nat)) (u : Nat) (ending : List (Nat × Nat) → Bool) :
    Nat → Nat → List (Nat × Nat) → List Nat → List (List (Nat × Nat))
  | 0,_,acc,_ => if ending acc then [acc] else []
  | fuel+1,lo,acc,st => opts.flatMap fun a =>
    if lo ≤ a.1 && a.2 &&& st.headD u == 0 then
      traverse opts u ending fuel a.1 (a::acc) (tick u a.2 st) else []

private theorem traverse_complete (opts : List (Nat × Nat)) (I : List (Nat × Nat)) (k : Nat) (hk : 0<k)
    (ending : List (Nat × Nat) → Bool) (next acc : List (Nat × Nat)) (lo : Nat)
    (hc : ∀ a∈next,a∈opts) (vals : ∀ a∈next,a.2=compat I a.1)
    (hl : ∀ a∈next,lo≤a.1) (hs : next.Pairwise (fun a b => a.1 ≤ b.1))
    (hg : ∀ u w,next=u++w → okContacts k I ((u.reverse++acc).map Prod.fst)) (hf : ending (next.reverse++acc)) :
    next.reverse++acc ∈ traverse opts (universal I) ending next.length lo acc (cells k I (acc.map Prod.fst) k 1) := by
  induction next generalizing acc lo with
  | nil => simpa [traverse,hf] using hf
  | cons a rest ih =>
    simp only [List.length_cons,traverse,List.mem_flatMap]
    refine ⟨a,hc a (by simp),?_⟩
    have hd : (cells k I (acc.map Prod.fst) k 1).headD (universal I)=threshold k I (acc.map Prod.fst) 1 := by
      cases k with | zero => omega | succ k => rfl
    have an := vals a (by simp)
    have allow := can_add k I (acc.map Prod.fst) a.1 (by simpa using hg [a] rest rfl)
    simp only [hl a (by simp),decide_true,Bool.true_and,an,hd,allow,beq_self_eq_true,if_true,tick_cells k I (acc.map Prod.fst) a.1 k 1 (by omega)]
    simpa [List.append_assoc] using ih (a::acc) a.1 (fun x hx => hc x (by simp [hx]))
      (fun x hx => vals x (by simp [hx])) (List.pairwise_cons.mp hs).1 (List.pairwise_cons.mp hs).2
      (by intro u w h; simpa [List.append_assoc] using hg (a::u) w (by simp [h]))
      (by simpa [List.append_assoc] using hf)


private def contactsOf {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (base front : List V) :=
  front.map fun x => bits (base.map fun y => decide (G.Adj x y))

private def usable (k d : Nat) (base : List Nat) : List Nat :=
  ((inds base).filter fun p => d ≤ p.2+1 && p.2+1 < k).map Prod.fst

private def guardRows (k : Nat) (base : List Nat) (isets : List (Nat × Nat)) (cs : List Nat) :=
  okContacts k isets cs && (degrees (shifted cs ++ base)).all (·<k)

private def tagged (k d : Nat) (base : List Nat) :=
  (usable k d base).map fun x => (x,compat (inds base) x)

private def assemble (k d : Nat) (base : List Nat) (opts : List (Nat × Nat)) (bits0 : Nat) (lims : List Nat) :=
  let ending := fun cs : List (Nat × Nat) => (degrees (attach (cs.reverse.map Prod.fst) base)).all (d≤·)
  (traverse opts bits0 ending d 0 [] lims).map (fun cs => attach (cs.reverse.map Prod.fst) base)

private def grow (k d : Nat) (base : List Nat) : List (List Nat) :=
  assemble k d base (tagged k d base) (universal (inds base)) (cells k (inds base) [] k 1)

private theorem grow_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k d : Nat) (ht : G.CliqueFree 3) (hs : Small G A k)
    (r : V) (front base : List V) (hn : (r::front++base).Nodup)
    (hall : (r::front++base).toFinset=A) (hd : front.length=d)
    (ha : ∀ x∈front,G.Adj r x) (hb : ∀ x∈base,¬G.Adj r x)
    (hcount : ∀ x∈front,d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k)
    (hmin : ∀ x∈A,d≤(A.filter (G.Adj x)).card)
    (horder : (contactsOf G base front).Pairwise (·≤·)) :
    encode G (r::front++base) ∈ grow k d (encode G base) := by
  let cs := contactsOf G base front
  have split := root_encoding G r front base ha hb ht
  change encode G (r::front++base) = attach cs (encode G base) at split
  have hbnd := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1
  have hc (s) (mem : s ∈ cs) : s ∈ usable k d (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    let S := base.toFinset.filter (G.Adj x)
    have row := inds_complete G base hbnd S (Finset.filter_subset ..) (neighbors_small G ht _ x)
    have m := hcount x hx
    rw [sizeAt_finset G hbnd] at m
    change bits (base.map fun y => decide (G.Adj x y)) ∈ _
    rw [row_mark]
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨row,by simpa [S] using m⟩,rfl⟩
  have guard_ (u w : List Nat) (h : cs=u++w) : guardRows k (encode G base) (inds (encode G base)) u := by
    let sl := front.take u.length
    have hu : contactsOf G base sl = u := by
      change (front.take u.length).map _=u
      rw [List.map_take, show front.map _=u++w from h, List.take_left]
    have ssub := (List.take_sublist u.length front).append (List.Sublist.refl base)
    have nodup : (sl++base).Nodup := (List.nodup_cons.mp hn).2.sublist ssub
    have sub : (sl++base).toFinset ⊆ A := by
      intro x hx
      rw [← hall]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (ssub.subset (List.mem_toFinset.mp hx)))
    have ha' (x) (hx : x∈sl) := ha x ((List.take_sublist u.length front).subset hx)
    have indep : Gᶜ.IsClique (sl.toFinset : Set V) := by
      rw [G.isClique_compl]
      intro x hx y hy hxy
      exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x (List.mem_toFinset.mp hx)) (ha' y (List.mem_toFinset.mp hy)) hxy
    have em := contacts G sl base (by intro x hx y hy adj; exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x hx) (ha' y hy) adj.ne adj)
    change encode G (sl++base)=shifted (contactsOf G base sl)++encode G base at em
    rw [← hu]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ok_contacts G A k hs sl base nodup sub indep,?_⟩
    rw [← em]
    exact degrees_bound G ht A k hs _ nodup sub
  have final_ : (degrees (attach cs (encode G base))).all (d≤·) = true := by
    rw [← split,degrees_encode,List.all_eq_true]
    intro n hh
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hh
    simpa only [decide_eq_true_eq,sizeAt_finset G hn,hall] using hmin x (hall ▸ List.mem_toFinset.mpr hx)
  have csl : cs.length=d := by simp [cs,contactsOf,hd]
  let base' := encode G base
  let tag (x : Nat) := (x,compat (inds base') x)
  let ts := cs.map tag
  have ret (ss : List Nat) : (ss.map tag).map Prod.fst = ss := by simp [tag,Function.comp_def]
  have tg (a) (ma : a∈ts) : a ∈ tagged k d base' := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ma
    exact List.mem_map.mpr ⟨x,hc x hx,rfl⟩
  have gg (u w : List (Nat × Nat)) (h : ts=u++w) : okContacts k (inds base') (u.reverse.map Prod.fst) := by
    let sl := cs.take u.length
    have split_ : cs=sl++cs.drop u.length := (List.take_append_drop u.length cs).symm
    have hu : sl.map tag=u := by
      change (cs.take u.length).map tag=u
      rw [List.map_take,show cs.map tag=u++w from h,List.take_left]
    have gh := Bool.and_eq_true_iff.mp (guard_ sl (cs.drop u.length) split_)
    rw [← hu,List.map_reverse,ret]
    simpa [okContacts] using gh.1
  have tslen : ts.length=d := by simp [ts,csl]
  have tsord : ts.Pairwise (fun a b => a.1 ≤ b.1) := List.pairwise_map.mpr horder
  rw [split]
  apply List.mem_map.mpr
  refine ⟨ts.reverse,?_,by simp [ts,ret]⟩
  have hk : 0<k := hs ∅ (by simp) (by simp)
  simpa only [List.append_nil,tslen,List.map_nil] using traverse_complete (tagged k d base') (inds base') k hk
    (fun u => (degrees (attach (u.reverse.map Prod.fst) base')).all (d≤·)) ts [] 0 tg
    (by intro a ha; obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha; rfl) (by simp) tsord
    (by simpa using gg) (by simpa only [List.append_nil,List.reverse_reverse,ts,ret,base'] using final_)

private def levels (norm : List Nat → List Nat) : Nat → Nat → Nat → List (List Nat)
  | 0,_,_ => []
  | k+1,n,cap => if n=0 then [[]] else
    ((List.range (min cap (min k (n-1)) + 1)).flatMap fun d =>
      (levels norm k (n-1-d) (k-1)).flatMap fun base => (grow (k+1) d base).map norm).eraseDups

private theorem sorted_neigh {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : Finset V) (base : List V) :
    ∃ l : List V, l.Nodup ∧ l.toFinset=N ∧ (contactsOf G base l).Pairwise (·≤·) := by
  let key (x : V) := bits (base.map fun y => decide (G.Adj x y))
  let ord (a b : V) := decide (key a ≤ key b)
  let l := N.toList.mergeSort ord
  have h := List.mergeSort_perm N.toList ord
  refine ⟨l,h.nodup_iff.mpr N.nodup_toList,?_,?_⟩
  · ext x
    simp [l]
  · have htr (a b c) : ord a b → ord b c → ord a c := by simp only [ord,decide_eq_true_eq]; omega
    have htot (a b) : ord a b || ord b a := by simp [ord,le_total]
    have sort_ := List.pairwise_mergeSort htr htot N.toList
    apply List.pairwise_map.mpr
    simpa only [ord,decide_eq_true_eq] using sort_

private theorem levels_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (norm : List Nat → List Nat)
    (hnorm : ∀ l : List V, ∃ l' : List V, l'.Perm l ∧ encode G l'=norm (encode G l))
    (k : Nat) (A : Finset V) (cap : Nat) (hs : Small G A k)
    (hu : A.Nonempty → ∃ x∈A,(A.filter (G.Adj x)).card ≤ cap) :
    ∃ vs : List V, vs.Nodup ∧ vs.toFinset=A ∧ encode G vs ∈ levels norm k A.card cap := by
  induction k generalizing A cap with
  | zero => have h := hs ∅ (by simp) (by simp); simp at h
  | succ k ih =>
    by_cases empty : A=∅
    · subst A; exact ⟨[],by simp,by simp,by simp [encode,levels]⟩
    have non := Finset.nonempty_iff_ne_empty.mpr empty
    obtain ⟨r,hr,hmin⟩ := A.exists_min_image (fun x => (A.filter (G.Adj x)).card) non
    let N := A.filter (G.Adj r)
    let B := A \ insert r N
    let d := N.card
    have hNr : r∉N := by simp [N]
    have hNA : N⊆A := Finset.filter_subset ..
    have hBA : B⊆A := Finset.sdiff_subset
    have hu' : d≤cap := by obtain ⟨x,hx,hh⟩ := hu non; exact (hmin x hx).trans hh
    have hdk : d≤k := Nat.le_of_lt_succ (hs N hNA (neighbors_small G ht A r))
    have hBcard : B.card + d + 1 = A.card := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hr hNA)
      rw [Finset.card_insert_of_notMem hNr] at hh
      omega
    have rB : r∉B := by simp [B]
    have hbase (x) (hx : x∈B) : ¬G.Adj r x := by
      have h := Finset.mem_sdiff.mp hx
      exact fun ha => h.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h.1,ha⟩))
    have noK : Small G B k := by
      intro S hS hI
      have rn : r∉S := fun h => rB (hS h)
      have indep : Gᶜ.IsClique (insert r S : Finset V) := by
        rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem rn]
        exact ⟨hI,fun x hx => ⟨fun e => rn (e ▸ hx),hbase x (hS hx)⟩⟩
      have hh := hs (insert r S) (Finset.insert_subset hr (hS.trans hBA)) indep
      rw [Finset.card_insert_of_notMem rn] at hh
      omega
    obtain ⟨base,hbn,hb,cls⟩ := ih B (k-1) noK (by
      rintro ⟨x,hx⟩
      have mm := noK (B.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht B x)
      exact ⟨x,hx,by omega⟩)
    obtain ⟨front,hfn,hf,sorted_⟩ := sorted_neigh G N base
    have ha (x) (hx : x∈front) : G.Adj r x := (Finset.mem_filter.mp (hf ▸ List.mem_toFinset.mpr hx)).2
    have hnot (x) (hx : x∈base) := hbase x (hb ▸ List.mem_toFinset.mpr hx)
    have dl : front.length=d := by rw [← List.toFinset_card_of_nodup hfn,hf]
    have nodup : (r::front++base).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · change r ∉ front++base
        rw [List.mem_append,not_or]
        exact ⟨fun h => hNr (hf ▸ List.mem_toFinset.mpr h), fun h => rB (hb ▸ List.mem_toFinset.mpr h)⟩
      · exact List.nodup_append.mpr ⟨hfn,hbn,fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩
    have cover : (r::front++base).toFinset=A := by
      ext x
      simp only [List.toFinset_cons,List.toFinset_append,hf,hb,B,Finset.mem_insert,Finset.mem_union,Finset.mem_sdiff]
      have h1 : x=r → x∈A := fun h => h ▸ hr
      have h2 : x∈N → x∈A := fun h => hNA h
      grind
    have hcount (x) (hx : x∈front) : d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k+1 := by
      have xN : x∈N := hf ▸ List.mem_toFinset.mpr hx
      have adj := ha x hx
      have eq : A.filter (G.Adj x)=insert r (B.filter (G.Adj x)) := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_sdiff,B]
        constructor
        · rintro ⟨yA,xy⟩
          by_cases yr : y=r
          · exact Or.inl yr
          · exact Or.inr ⟨⟨yA,not_or.mpr ⟨yr,fun yN => G.isIndepSet_neighborSet_of_triangleFree ht r adj (Finset.mem_filter.mp yN).2 xy.ne xy⟩⟩,xy⟩
        · rintro (rfl|⟨⟨yA,_⟩,xy⟩)
          · exact ⟨hr,adj.symm⟩
          · exact ⟨yA,xy⟩
      have mm := hmin x (hNA xN)
      have mx := hs (A.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht A x)
      have rn : r∉B.filter (G.Adj x) := fun h => rB (Finset.mem_filter.mp h).1
      rw [eq,Finset.card_insert_of_notMem rn] at mm mx
      rw [sizeAt_finset G hbn,hb]
      exact ⟨mm,mx⟩
    have grown := grow_complete G A (k+1) d ht hs r front base nodup cover dl ha hnot hcount hmin sorted_
    obtain ⟨l,hperm,heq⟩ := hnorm (r::front++base)
    refine ⟨l,hperm.nodup_iff.mpr nodup,?_,?_⟩
    · rw [← cover]
      ext x
      exact List.mem_toFinset.trans (hperm.mem_iff.trans List.mem_toFinset.symm)
    · rw [heq,levels,if_neg (Finset.card_ne_zero.mpr non)]
      apply List.mem_eraseDups.mpr
      apply List.mem_flatMap.mpr
      refine ⟨d,List.mem_range.mpr (by omega),List.mem_flatMap.mpr ⟨encode G base,?_,List.mem_map.mpr ⟨_,grown,rfl⟩⟩⟩
      simpa only [show A.card-1-d=B.card by omega] using cls


private def swapAt {α : Type*} : Nat → List α → List α
  | 0,x::y::xs => y::x::xs
  | i+1,x::xs => x::swapAt i xs
  | _,l => l

private theorem swap_perm {α : Type*} (i : Nat) (l : List α) : (swapAt i l).Perm l := by
  induction i generalizing l with
  | zero => cases l with | nil => rfl | cons a l => cases l with | nil => rfl | cons b l => exact List.Perm.swap a b l
  | succ i ih => cases l with | nil => rfl | cons a l => exact List.Perm.cons a (ih l)

private def exchange : Nat → Nat → Nat
  | 0,x => 4*(x/4)+2*(x%2)+((x/2)%2)
  | i+1,x => 2*exchange i (x/2)+x%2

private theorem bits_swap (i : Nat) (l : List Bool) (h : i+2≤l.length) :
    bits (swapAt i l)=exchange i (bits l) := by
  induction i generalizing l with
  | zero =>
    obtain ⟨a,b,l,rfl⟩ : ∃ a b t,l=a::b::t := by cases l with | nil => simp at h | cons a l => cases l with | nil => simp at h | cons b t => exact ⟨_,_,_,rfl⟩
    cases a <;> cases b <;> simp [swapAt,bits,exchange] <;> omega
  | succ i ih =>
    cases l with
    | nil => simp at h
    | cons a t =>
      have e := ih t (by simp at h; omega)
      cases a <;> simp [swapAt,bits,exchange,half_step,e]

private theorem swap_map {α β : Type*} (f : α→β) (i : Nat) (l : List α) :
    (swapAt i l).map f=swapAt i (l.map f) := by
  induction i generalizing l with
  | zero => cases l with | nil => rfl | cons a l => cases l <;> rfl
  | succ i ih => cases l with | nil => rfl | cons a l => simp [swapAt,ih]

private def swapCode : Nat → List Nat → List Nat
  | 0,p::q::rs => (p%2+2*q)::(p/2)::rs
  | i+1,p::rs => exchange i p :: swapCode i rs
  | _,l => l

private theorem swap_encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Nat) (l : List V) (h : i+2≤l.length) : encode G (swapAt i l) = swapCode i (encode G l) := by
  induction i generalizing l with
  | zero =>
    obtain ⟨a,b,t,rfl⟩ : ∃ a b t,l=a::b::t := by cases l with | nil => simp at h | cons a l => cases l with | nil => simp at h | cons b t => exact ⟨_,_,_,rfl⟩
    by_cases adj : G.Adj a b <;> simp [swapAt,swapCode,encode,bits,adj,G.adj_comm b a,Nat.add_comm]
    omega
  | succ i ih =>
    cases l with
    | nil => simp at h
    | cons a t =>
      have hi : i+2≤t.length := by simp at h; omega
      simp only [swapAt,encode,swap_map,swapCode,List.cons.injEq]
      exact ⟨bits_swap i _ (by simpa using hi),ih t hi⟩

private def relabel (swaps rows : List Nat) :=
  swaps.foldl (fun l i => if i+2≤l.length then swapCode i l else l) rows

private theorem relabel_real {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (swaps : List Nat) (l : List V) : ∃ l', l'.Perm l ∧ encode G l'=relabel swaps (encode G l) := by
  induction swaps generalizing l with
  | nil => exact ⟨l,.refl _,rfl⟩
  | cons i is ih =>
    by_cases hi : i+2≤l.length
    · obtain ⟨t,ht,he⟩ := ih (swapAt i l)
      exact ⟨t,ht.trans (swap_perm ..),by simpa [relabel,encode_length,hi,swap_encode G i l hi] using he⟩
    · simpa [relabel,encode_length,hi] using ih l


private def renumber : List Nat → List Nat
  | [1,2,1,0] => [2]
  | [1,2,3,2,2,1,0] => [2,4]
  | [1,4,3,2,2,1,0] => [3,2,5,4]
  | [1,8,3,2,2,1,0] => [4,3,2,3,5,4]
  | [1,9,3,2,2,1,0] => [2,4]
  | [1,12,3,2,2,1,0] => [5,4,3,2,4,3,5,4]
  | [1,16,3,2,2,1,0] => [5,4,3,2,4,3,5,4]
  | [1,17,3,2,2,1,0] => [3,2,5,4]
  | [1,18,3,2,2,1,0] => [4,3,2,3,5,4]
  | [3,2,2,3,2,1,0] => [5,4,3,2,1,0,5,4,3,2,1,5,4,3,2,5,4,3,4]
  | [3,2,4,3,2,1,0] => [5,4,3,2,1,0,4,3,2,1,5,4,3,2,5,4,3,4]
  | [3,2,6,3,2,1,0] => [5,4,3,2,1,0,4,3,2,1,5,4,3,2,4,3]
  | [3,2,10,1,1,1,0] => [4,3,2,1,0,5,4,3,2,1,5,4,3,2,4,3]
  | [3,4,8,3,2,1,0] => [4,3,2,1,0,3,2,1,5,4,3,2,5,4,3,4]
  | [3,4,9,1,1,1,0] => [2,1,0,2,1,3,2,5]
  | [3,4,9,3,2,1,0] => [4,3,2,1,0,3,2,1,5,4,3,2,4,3]
  | [3,4,9,3,2,2,1,0] => [3,5]
  | [3,8,8,3,2,1,0] => [3,2,1,0,3,2,1,5,4,3,2,5,4,3,4]
  | [3,8,9,1,1,1,0] => [5,4,3,2,1,0,2,1,5,4,3,2]
  | [3,8,9,3,2,1,0] => [3,2,1,0,3,2,1,5,4,3,2,4,3]
  | [3,8,17,3,2,2,1,0] => [4,3,6,5]
  | [3,10,8,1,1,1,0] => [3,2,1,0,3,2,1,4,3,2,3]
  | [3,10,10,1,1,1,0] => [2,1,0,3,2,1,2,4,3,5,4,5]
  | [3,12,8,3,2,1,0] => [2,1,0,3,2,1,4,3,2,3]
  | [3,12,9,1,0,1,0] => [1,5]
  | [3,12,17,3,2,2,1,0] => [4,6]
  | [3,16,9,1,1,1,0] => [0,5,4,3,2]
  | [3,16,18,3,2,2,1,0] => [5,4,3,4,6,5]
  | [3,18,10,1,1,1,0] => [1,5,4,3,5,4,5]
  | [3,18,18,3,2,2,1,0] => [3,5,4,6]
  | [3,24,16,3,2,2,1,0] => [1,6,5,4,3,5,4,6,5]
  | [3,24,17,3,2,2,1,0] => [6,5,4,3,5,4,6,5]
  | [3,24,18,3,2,2,1,0] => [6,5,4,3,6,5,4,6,5,6]
  | [7,24,66,137,3,12,9,3,2,2,1,0] => [0,4,3,2,5,4,3,5,4,8,7,10,9]
  | [7,24,130,145,3,12,9,3,2,2,1,0] => [0,5,4,3,2,5,4,3,5,4,9,8,7,8,10,9]
  | [7,24,146,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,24,194,129,3,2,6,3,2,2,1,0] => [2,8,10]
  | [7,24,194,129,3,12,9,3,2,2,1,0] => [0,5,4,3,2,5,4,3,5,4,5,10,9,8,7,9,8,10,9]
  | [7,24,194,137,3,2,6,3,2,2,1,0] => [2,8,10]
  | [7,24,194,137,3,12,9,3,2,2,1,0] => [7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,7,6,5,4,3,9,8,7,6,5,4,10,9,8,7,6,5,7,6,8,7,9,8,10]
  | [7,24,194,145,3,12,9,3,2,2,1,0] => [6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,8,7,6,5,4,3,9,8,7,6,5,4,10,9,8,7,6,5,7,6,8,7,9,8,10]
  | [7,36,132,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,36,140,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,36,196,130,3,2,6,3,2,2,1,0] => [2,4,6,8,10]
  | [7,36,196,134,3,2,6,3,2,2,1,0] => [2,4,6,8,10]
  | [7,36,196,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,260,140,144,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,260,140,145,3,2,6,3,2,2,1,0] => [4,3,2,1,0,6,5,4,3,2,1,3,2,5,4,3,6,5,4,8,7,6,5,8,7,6,10,9,8,7,9,8,10,9]
  | [7,260,140,146,3,2,6,3,2,2,1,0] => [3,2,1,0,1,4,3,2,5,4,3,4,9,8,7,6,8,10,9]
  | [7,260,268,145,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,260,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,264,146,144,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,264,146,145,3,2,6,3,2,2,1,0] => [4,3,2,1,0,1,4,3,2,6,5,4,3,4,9,8,7,6,8,10,9]
  | [7,264,146,146,3,2,6,3,2,2,1,0] => [3,2,1,0,5,4,3,2,1,3,2,5,4,3,6,5,4,8,7,6,5,8,7,6,10,9,8,7,9,8,10,9]
  | [7,264,274,146,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,280,146,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,280,146,146,3,2,6,3,2,2,1,0] => [1,4,6]
  | [7,280,194,129,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,280,194,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,280,194,145,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,280,194,146,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,280,274,146,3,2,6,3,2,2,1,0] => [1,2,4,6,8,10]
  | [7,292,196,130,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,292,196,134,3,2,6,3,2,2,1,0] => [4,6]
  | [7,292,196,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,292,196,145,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,292,196,146,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,292,268,145,3,2,6,3,2,2,1,0] => [1,2,8,10]
  | [7,292,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,384,258,134,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,258,134,3,12,9,3,2,2,1,0] => [0,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,8]
  | [7,384,260,137,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,384,260,145,3,12,9,3,2,2,1,0] => [0,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,7,10,9,8,10]
  | [7,384,264,137,3,12,9,3,2,2,1,0] => [0,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,8,7,9,8,10]
  | [7,384,268,137,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,268,137,3,12,9,3,2,2,1,0] => [7,6,5,4,3,2,1,0,5,4,3,2,1,7,6,5,4,3,2,9,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,7,6,8,7,10,9,8,10]
  | [7,384,268,145,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,268,145,3,12,9,3,2,2,1,0] => [6,5,4,3,2,1,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,7,6,8,7,10,9,8,10]
  | [7,384,274,146,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,384,274,148,3,12,9,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,384,276,145,3,12,9,3,2,2,1,0] => [10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,388,258,134,3,2,6,3,2,2,1,0] => [4,3,2,1,0,6,5,4,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,9,8,7,8,10,9]
  | [7,388,260,137,3,2,6,3,2,2,1,0] => [4,3,2,1,0,2,1,4,3,2,6,5,4,3,5,4,10,9,8,7,6,9,8,10,9]
  | [7,388,260,145,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,388,264,137,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,388,268,137,3,2,6,3,2,2,1,0] => [1,2,8,10]
  | [7,388,268,145,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,388,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,388,274,146,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,388,274,148,3,12,9,3,2,2,1,0] => [2,1,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,388,276,145,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,392,258,134,3,2,6,3,2,2,1,0] => [3,2,1,0,2,1,4,3,2,5,4,3,5,4,10,9,8,7,6,9,8,10,9]
  | [7,392,260,137,3,2,6,3,2,2,1,0] => [3,2,1,0,5,4,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,9,8,7,8,10,9]
  | [7,392,268,137,3,2,6,3,2,2,1,0] => [2,1,2,4,6,8,10]
  | [7,392,268,145,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,392,274,146,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [15,304,164,162,82,3,2,9,1,1,1,0] => [2,1,0,10,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,6,5,4,3,6,5,7,6,8,7,9,10]
  | [15,304,196,138,73,1,6,3,2,2,1,0] => [2,1,3,2,8,10]
  | [15,584,392,268,145,3,2,6,3,2,2,1,0] => [5,7]
  | _ => []

private def normalized (g : List Nat) := relabel (renumber g) g

private def roots0 : List (List Nat) := []
private def roots1 : List (List Nat) := []
private def roots2 : List (List Nat) := []
private def roots3 : List (List Nat) := [[15,560,388,274,146,3,2,6,3,2,2,1,0]]
private def roots4 : List (List Nat) := [[7,24,130,145,3,2,6,3,2,2,1,0],
  [7,24,146,145,3,2,6,3,2,2,1,0],
  [7,24,194,145,3,2,6,3,2,2,1,0],
  [7,280,146,145,3,2,6,3,2,2,1,0],
  [7,280,194,137,3,2,6,3,2,2,1,0],
  [7,24,98,137,3,12,9,3,2,2,1,0],
  [7,132,268,137,3,12,9,3,2,2,1,0],
  [7,196,268,137,3,12,9,3,2,2,1,0],
  [7,388,258,134,3,12,9,3,2,2,1,0],
  [7,388,268,137,3,12,9,3,2,2,1,0],
  [15,296,196,140,73,1,6,3,2,2,1,0],
  [15,352,196,146,82,3,10,10,1,0,1,0]]

theorem degrees_length (g : List Nat) : (degrees g).length=g.length := by
  have step (xs : List Nat) (m : Nat) : (bump m xs).length=xs.length := by
    induction xs generalizing m with | nil => rfl | cons a xs ih => simp [bump,ih]
  induction g with | nil => rfl | cons a g ih => simp [degrees,step,ih]

theorem bump_sum (xs : List Nat) (m : Nat) : (bump m xs).sum=xs.sum+countBits xs.length m := by
  induction xs generalizing m with | nil => rfl | cons a xs ih => simp [bump,countBits,ih]; omega

def edges_ : List Nat → Nat
  | [] => 0
  | m::t => countBits t.length m + edges_ t

theorem energy (rows : List Nat) : (degrees rows).sum=2*edges_ rows := by
  induction rows with
  | nil => rfl
  | cons m t ih => simp [degrees,edges_,bump_sum,degrees_length,ih]; omega

theorem count_shift (n a j : Nat) : countBits (j+n) (2^j*a)=countBits n a := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : 2^(j+1)*a=2*(2^j*a) := by rw [pow_succ]; ring
    rw [Nat.succ_add,countBits,e]
    simp [ih]

theorem count_full (d n : Nat) : countBits (d+n) (2^d-1)=d := by
  induction d with
  | zero =>
    have h (t : Nat) : countBits t 0=0 := by induction t with | zero => rfl | succ k ih => simp [countBits,ih]
    simp [h]
  | succ d ih =>
    have hp : 0 < 2^d := Nat.two_pow_pos _
    have split : 2^(d+1)-1=2*(2^d-1)+1 := by rw [pow_succ]; omega
    rw [Nat.succ_add,countBits,split,half_step,ih]
    omega

theorem shifted_length (xs : List Nat) : (shifted xs).length=xs.length := by
  induction xs with | nil => rfl | cons a xs ih => simp [shifted,ih]

theorem edges_attached (xs b : List Nat) : edges_ (attach xs b) =
    xs.length + (xs.map (countBits b.length)).sum + edges_ b := by
  have h (ls : List Nat) : edges_ (shifted ls++b)=(ls.map (countBits b.length)).sum+edges_ b := by
    induction ls with
    | nil => simp [shifted]
    | cons a ls ih => simp [shifted,edges_,shifted_length,count_shift,ih,Nat.add_assoc]
  simp [attach,edges_,shifted_length,count_full,h,Nat.add_assoc]

def Extension (k d : Nat) (b cs : List Nat) : Prop :=
  cs.length = d ∧ (∀ x ∈ cs, x ∈ usable k d b) ∧ okContacts k (inds b) cs = true ∧ cs.Pairwise (· ≤ ·)
theorem graphExtension {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k d : Nat) (ht : G.CliqueFree 3) (hs : Small G A k)
    (r : V) (front base : List V) (hn : (r::front++base).Nodup)
    (hall : (r::front++base).toFinset=A) (hd : front.length=d)
    (ha : ∀ x∈front,G.Adj r x) (hb : ∀ x∈base,¬G.Adj r x)
    (hcount : ∀ x∈front,d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k)
    (hmin : ∀ x∈A,d≤(A.filter (G.Adj x)).card)
    (horder : (contactsOf G base front).Pairwise (·≤·)) :
    ∃ cs, Extension k d (encode G base) cs ∧ encode G (r::front++base) = attach cs (encode G base) := by
  let cs := contactsOf G base front
  have split := root_encoding G r front base ha hb ht
  change encode G (r::front++base) = attach cs (encode G base) at split
  have hbnd := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1
  have hc (s) (mem : s ∈ cs) : s ∈ usable k d (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    let S := base.toFinset.filter (G.Adj x)
    have row := inds_complete G base hbnd S (Finset.filter_subset ..) (neighbors_small G ht _ x)
    have m := hcount x hx
    rw [sizeAt_finset G hbnd] at m
    change bits (base.map fun y => decide (G.Adj x y)) ∈ _
    rw [row_mark]
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨row,by simpa [S] using m⟩,rfl⟩
  have guard_ (u w : List Nat) (h : cs=u++w) : guardRows k (encode G base) (inds (encode G base)) u := by
    let sl := front.take u.length
    have hu : contactsOf G base sl = u := by
      change (front.take u.length).map _=u
      rw [List.map_take, show front.map _=u++w from h, List.take_left]
    have ssub := (List.take_sublist u.length front).append (List.Sublist.refl base)
    have nodup : (sl++base).Nodup := (List.nodup_cons.mp hn).2.sublist ssub
    have sub : (sl++base).toFinset ⊆ A := by
      intro x hx
      rw [← hall]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (ssub.subset (List.mem_toFinset.mp hx)))
    have ha' (x) (hx : x∈sl) := ha x ((List.take_sublist u.length front).subset hx)
    have indep : Gᶜ.IsClique (sl.toFinset : Set V) := by
      rw [G.isClique_compl]
      intro x hx y hy hxy
      exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x (List.mem_toFinset.mp hx)) (ha' y (List.mem_toFinset.mp hy)) hxy
    have em := contacts G sl base (by intro x hx y hy adj; exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x hx) (ha' y hy) adj.ne adj)
    change encode G (sl++base)=shifted (contactsOf G base sl)++encode G base at em
    rw [← hu]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ok_contacts G A k hs sl base nodup sub indep,?_⟩
    rw [← em]
    exact degrees_bound G ht A k hs _ nodup sub
  exact ⟨cs, ⟨by simp [cs,contactsOf,hd], hc,
    (Bool.and_eq_true_iff.mp (guard_ cs [] (by simp))).1, horder⟩, split⟩

theorem rootSplitting {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (norm : List Nat → List Nat)
    (hnorm : ∀ l : List V, ∃ l' : List V, l'.Perm l ∧ encode G l'=norm (encode G l))
    (k : Nat) (A : Finset V) (non : A.Nonempty) (cap : Nat) (hs : Small G A (k+1))
    (hu : A.Nonempty → ∃ x∈A,(A.filter (G.Adj x)).card ≤ cap) :
    ∃ (vs : List V) (d : Nat) (b cs : List Nat), vs.Nodup ∧ vs.toFinset=A ∧ d≤cap ∧
      b∈levels norm k (A.card-1-d) (k-1) ∧ Extension (k+1) d b cs ∧ encode G vs=attach cs b ∧ ∃ r ∈ A, (A.filter (G.Adj r)).card = d := by
    obtain ⟨r,hr,hmin⟩ := A.exists_min_image (fun x => (A.filter (G.Adj x)).card) non
    let N := A.filter (G.Adj r)
    let B := A \ insert r N
    let d := N.card
    have hNr : r∉N := by simp [N]
    have hNA : N⊆A := Finset.filter_subset ..
    have hBA : B⊆A := Finset.sdiff_subset
    have hu' : d≤cap := by obtain ⟨x,hx,hh⟩ := hu non; exact (hmin x hx).trans hh
    have hdk : d≤k := Nat.le_of_lt_succ (hs N hNA (neighbors_small G ht A r))
    have hBcard : B.card + d + 1 = A.card := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hr hNA)
      rw [Finset.card_insert_of_notMem hNr] at hh
      omega
    have rB : r∉B := by simp [B]
    have hbase (x) (hx : x∈B) : ¬G.Adj r x := by
      have h := Finset.mem_sdiff.mp hx
      exact fun ha => h.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h.1,ha⟩))
    have noK : Small G B k := by
      intro S hS hI
      have rn : r∉S := fun h => rB (hS h)
      have indep : Gᶜ.IsClique (insert r S : Finset V) := by
        rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem rn]
        exact ⟨hI,fun x hx => ⟨fun e => rn (e ▸ hx),hbase x (hS hx)⟩⟩
      have hh := hs (insert r S) (Finset.insert_subset hr (hS.trans hBA)) indep
      rw [Finset.card_insert_of_notMem rn] at hh
      omega
    obtain ⟨base,hbn,hb,cls⟩ := levels_complete G ht norm hnorm k B (k-1) noK (by
      rintro ⟨x,hx⟩
      have mm := noK (B.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht B x)
      exact ⟨x,hx,by omega⟩)
    obtain ⟨front,hfn,hf,sorted_⟩ := sorted_neigh G N base
    have ha (x) (hx : x∈front) : G.Adj r x := (Finset.mem_filter.mp (hf ▸ List.mem_toFinset.mpr hx)).2
    have hnot (x) (hx : x∈base) := hbase x (hb ▸ List.mem_toFinset.mpr hx)
    have dl : front.length=d := by rw [← List.toFinset_card_of_nodup hfn,hf]
    have nodup : (r::front++base).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · change r ∉ front++base
        rw [List.mem_append,not_or]
        exact ⟨fun h => hNr (hf ▸ List.mem_toFinset.mpr h), fun h => rB (hb ▸ List.mem_toFinset.mpr h)⟩
      · exact List.nodup_append.mpr ⟨hfn,hbn,fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩
    have cover : (r::front++base).toFinset=A := by
      ext x
      simp only [List.toFinset_cons,List.toFinset_append,hf,hb,B,Finset.mem_insert,Finset.mem_union,Finset.mem_sdiff]
      have h1 : x=r → x∈A := fun h => h ▸ hr
      have h2 : x∈N → x∈A := fun h => hNA h
      grind
    have hcount (x) (hx : x∈front) : d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k+1 := by
      have xN : x∈N := hf ▸ List.mem_toFinset.mpr hx
      have adj := ha x hx
      have eq : A.filter (G.Adj x)=insert r (B.filter (G.Adj x)) := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_sdiff,B]
        constructor
        · rintro ⟨yA,xy⟩
          by_cases yr : y=r
          · exact Or.inl yr
          · exact Or.inr ⟨⟨yA,not_or.mpr ⟨yr,fun yN => G.isIndepSet_neighborSet_of_triangleFree ht r adj (Finset.mem_filter.mp yN).2 xy.ne xy⟩⟩,xy⟩
        · rintro (rfl|⟨⟨yA,_⟩,xy⟩)
          · exact ⟨hr,adj.symm⟩
          · exact ⟨yA,xy⟩
      have mm := hmin x (hNA xN)
      have mx := hs (A.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht A x)
      have rn : r∉B.filter (G.Adj x) := fun h => rB (Finset.mem_filter.mp h).1
      rw [eq,Finset.card_insert_of_notMem rn] at mm mx
      rw [sizeAt_finset G hbn,hb]
      exact ⟨mm,mx⟩
    obtain ⟨cs,hcs,enc⟩ := graphExtension G A (k+1) d ht hs r front base nodup cover dl ha hnot hcount hmin sorted_
    exact ⟨r::front++base, d, encode G base, cs, nodup, cover, hu', by simpa only [show A.card-1-d=B.card by omega] using cls, hcs, enc, ⟨r, hr, rfl⟩⟩


private abbrev WeightedRow := (Nat × Nat) × Nat

private def rowScore (W : List WeightedRow) (x : Nat) : Nat :=
  ((W.filter (fun w => x &&& w.1.1 == 0)).map Prod.snd).sum

private def rowCapacity (W : List WeightedRow) : Nat :=
  (W.map fun w => (5-w.1.2)*w.2).sum

private def penalty (f : Nat → Bool) (x : Nat) := (f x).toNat

private theorem rowScore_cons (w : WeightedRow) (W : List WeightedRow) (cs : List Nat) :
    (cs.map (rowScore (w::W))).sum =
    (cs.filter (fun x => x &&& w.1.1 == 0)).length*w.2 + (cs.map (rowScore W)).sum := by
  induction cs with
  | nil => simp
  | cons x cs ih =>
    by_cases e : x &&& w.1.1 = 0
    · simp [rowScore,e,Nat.succ_mul] at ih ⊢
      omega
    · simp [rowScore,e] at ih ⊢
      omega

private theorem rowScore_le (b cs : List Nat) (W : List WeightedRow)
    (valid : ∀ w∈W,w.1∈inds b) (good : okContacts 6 (inds b) cs=true) :
    (cs.map (rowScore W)).sum ≤ rowCapacity W := by
  induction W with
  | nil =>
    have h : rowScore [] = fun _ => 0 := rfl
    simp [h,rowCapacity]
  | cons w W ih =>
    have sub := ih (fun t ht => valid t (.tail _ ht))
    have hm := of_decide_eq_true (List.all_eq_true.mp good w.1 (valid w (.head _)))
    have lecap : (cs.filter (fun x => x &&& w.1.1 == 0)).length ≤ 5-w.1.2 := by omega
    have lh := Nat.mul_le_mul_right w.2 lecap
    rw [rowScore_cons]
    change _ ≤ (5-w.1.2)*w.2 + rowCapacity W
    omega

private theorem rowScore_ge (b : List Nat) (f : Nat → Bool) (edgeWeight extraWeight low : Nat) (W : List WeightedRow)
    (cs : List Nat) (h : ∀ x∈cs, low ≤ countBits b.length x * edgeWeight + penalty f x * extraWeight + rowScore W x) :
    cs.length*low ≤ (cs.map (countBits b.length)).sum * edgeWeight +
      (cs.map (penalty f)).sum * extraWeight + (cs.map (rowScore W)).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hh := ih (fun x hx => h x (.tail _ hx))
    have hc := h c (.head _)
    simp only [List.length_cons,Nat.succ_mul,List.map_cons,List.sum_cons,Nat.add_mul]
    omega


private def dualCheckSimple (limit : Nat) (b : List Nat) (d edgeWeight low : Nat)
    (W : List WeightedRow) : Bool :=
  W.all (fun w => decide (w.1 ∈ inds b)) &&
  (usable 6 d b).all (fun x => decide (low ≤ countBits b.length x * edgeWeight + rowScore W x)) &&
  decide ((limit - edges_ b - d) * edgeWeight + rowCapacity W < d * low)

private theorem viaDualImpossible (b cs : List Nat) (d low : Nat) (W : List WeightedRow)
    (ext : Extension 6 d b cs)
    (check : dualCheckSimple 0 b d 0 low W = true) : False := by
  obtain ⟨len, mem, good, _⟩ := ext
  obtain ⟨both, last⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨valid, opts⟩ := Bool.and_eq_true_iff.mp both
  have upper := rowScore_le b cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  have lower := rowScore_ge b (fun _ => false) 0 0 low W cs (fun x hx => by
    have hx' := of_decide_eq_true (List.all_eq_true.mp opts x (mem x hx))
    simp only [Nat.mul_zero, Nat.zero_add] at hx' ⊢
    exact hx')
  simp only [Nat.mul_zero, Nat.zero_add] at lower
  have hl := of_decide_eq_true last
  simp only [Nat.mul_zero, Nat.zero_add] at hl
  rw [len] at lower
  omega

private theorem viaDual32 (b cs : List Nat) (d edgeWeight low : Nat) (W : List WeightedRow)
    (ext : Extension 6 d b cs)
    (check : dualCheckSimple 31 b d edgeWeight low W = true) :
    32 ≤ edges_ (attach cs b) := by
  by_contra! small
  obtain ⟨len, mem, good, _⟩ := ext
  obtain ⟨both, last⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨valid, opts⟩ := Bool.and_eq_true_iff.mp both
  have upper := rowScore_le b cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  have lower := rowScore_ge b (fun _ => false) edgeWeight 0 low W cs (fun x hx => by
    have hx' := of_decide_eq_true (List.all_eq_true.mp opts x (mem x hx))
    simp only [Nat.mul_zero, Nat.add_zero]
    exact hx')
  simp only [Nat.mul_zero, Nat.add_zero] at lower
  rw [edges_attached, len] at small
  have e : (cs.map (countBits b.length)).sum ≤ 31 - edges_ b - d := by omega
  have he := Nat.mul_le_mul_right edgeWeight e
  have hl := of_decide_eq_true last
  rw [len] at lower
  omega

private def allInd4 (b : List Nat) : List WeightedRow :=
  ((inds b).filter (fun p => p.2 == 4)).map (fun p => (p, 1))

private abbrev b3_0 : List Nat := [15,560,388,274,146,3,2,6,3,2,2,1,0]
private abbrev b4_0 : List Nat := [7,24,130,145,3,2,6,3,2,2,1,0]
private abbrev b4_1 : List Nat := [7,24,146,145,3,2,6,3,2,2,1,0]
private abbrev b4_2 : List Nat := [7,24,194,145,3,2,6,3,2,2,1,0]
private abbrev b4_3 : List Nat := [7,280,146,145,3,2,6,3,2,2,1,0]
private abbrev b4_4 : List Nat := [7,280,194,137,3,2,6,3,2,2,1,0]
private abbrev b4_5 : List Nat := [7,24,98,137,3,12,9,3,2,2,1,0]
private abbrev b4_6 : List Nat := [7,132,268,137,3,12,9,3,2,2,1,0]
private abbrev b4_7 : List Nat := [7,196,268,137,3,12,9,3,2,2,1,0]
private abbrev b4_8 : List Nat := [7,388,258,134,3,12,9,3,2,2,1,0]
private abbrev b4_9 : List Nat := [7,388,268,137,3,12,9,3,2,2,1,0]
private abbrev b4_10 : List Nat := [15,296,196,140,73,1,6,3,2,2,1,0]
private abbrev b4_11 : List Nat := [15,352,196,146,82,3,10,10,1,0,1,0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem smaller3 : (levels normalized 5 13 4).all (fun b => decide (b ∈ roots3)) = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem smaller4 : (levels normalized 5 12 4).all (fun b => decide (b ∈ roots4)) = true := by
  decide +kernel

/- Degree-4 case of R(3,6) = 18: b3_0 has no d=4 extension. -/

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b3_0_deg4_cert : dualCheckSimple 0 b3_0 4 0 11 (allInd4 b3_0) = true := by
  decide +kernel

theorem no_deg4_18 (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 6)
    (hmin : ∀ v, 4 ≤ G.degree v) (h4 : ∃ v, G.degree v = 4) : False := by
  classical
  let U : Finset (Fin 18) := Finset.univ
  have bounded : Small G U 6 := by
    intro I _ hI
    by_contra! hc
    exact (hi.mono hc) I ⟨hI, rfl⟩
  have low : U.Nonempty → ∃ x ∈ U, (U.filter (G.Adj x)).card ≤ 4 := by
    intro _
    obtain ⟨v, hv⟩ := h4
    refine ⟨v, Finset.mem_univ v, ?_⟩
    simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]
    omega
  have hn (l : List (Fin 18)) := relabel_real G (renumber (encode G l)) l
  obtain ⟨vs, d, b, cs, _, _, hd, hb, hcs, _, ⟨r, _, hr⟩⟩ :=
    rootSplitting G ht normalized hn 5 U (by simp [U]) 4 bounded low
  have hdlb : 4 ≤ d := by
    have hmr := hmin r
    simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree] at hr
    omega
  have hdeq : d = 4 := by omega
  subst hdeq
  have hb' : b ∈ levels normalized 5 13 4 := by simpa [U] using hb
  have ok := of_decide_eq_true (List.all_eq_true.mp smaller3 b hb')
  simp only [roots3, List.mem_cons, List.not_mem_nil, or_false] at ok
  subst ok
  exact viaDualImpossible b3_0 cs 4 11 (allInd4 b3_0) hcs b3_0_deg4_cert


/- Zero-branching dual certificates for 40 <= edges and 41 <= edges on 17-vertex (3,6)-graphs. -/

private def dualCheck40 (b : List Nat) (d : Nat) (f : Nat → Bool)
    (cap edgeWeight extraWeight low : Nat) (W : List WeightedRow) : Bool :=
  W.all (fun w => decide (w.1 ∈ inds b)) &&
  (usable 6 d b).all (fun x => decide
    (low ≤ countBits b.length x * edgeWeight + penalty f x * extraWeight + rowScore W x)) &&
  decide ((39 - edges_ b - d) * edgeWeight + cap * extraWeight + rowCapacity W < d * low)

private theorem viaDual40 (b cs : List Nat) (d : Nat) (ext : Extension 6 d b cs)
    (f : Nat → Bool) (cap edgeWeight extraWeight low : Nat) (W : List WeightedRow)
    (check : dualCheck40 b d f cap edgeWeight extraWeight low W = true)
    (bound : (cs.map (penalty f)).sum ≤ cap) :
    40 ≤ edges_ (attach cs b) := by
  by_contra! small
  obtain ⟨len, mem, good, _⟩ := ext
  obtain ⟨both, last⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨valid, opts⟩ := Bool.and_eq_true_iff.mp both
  have upper := rowScore_le b cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  have lower := rowScore_ge b f edgeWeight extraWeight low W cs
    (fun x hx => of_decide_eq_true (List.all_eq_true.mp opts x (mem x hx)))
  rw [edges_attached, len] at small
  have e : (cs.map (countBits b.length)).sum ≤ 39 - edges_ b - d := by omega
  have he := Nat.mul_le_mul_right edgeWeight e
  have hf := Nat.mul_le_mul_right extraWeight bound
  have hl := of_decide_eq_true last
  rw [len] at lower
  omega

private def dualCheck41Pen (b : List Nat) (d : Nat) (f : Nat → Bool)
    (cap edgeWeight extraWeight low : Nat) (W : List WeightedRow) : Bool :=
  W.all (fun w => decide (w.1 ∈ inds b)) &&
  (usable 6 d b).all (fun x => decide
    (low ≤ countBits b.length x * edgeWeight + penalty f x * extraWeight + rowScore W x)) &&
  decide ((40 - edges_ b - d) * edgeWeight + cap * extraWeight + rowCapacity W < d * low)

private theorem viaDual41Pen (b cs : List Nat) (d : Nat) (ext : Extension 6 d b cs)
    (f : Nat → Bool) (cap edgeWeight extraWeight low : Nat) (W : List WeightedRow)
    (check : dualCheck41Pen b d f cap edgeWeight extraWeight low W = true)
    (bound : (cs.map (penalty f)).sum ≤ cap) :
    41 ≤ edges_ (attach cs b) := by
  by_contra! small
  obtain ⟨len, mem, good, _⟩ := ext
  obtain ⟨both, last⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨valid, opts⟩ := Bool.and_eq_true_iff.mp both
  have upper := rowScore_le b cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  have lower := rowScore_ge b f edgeWeight extraWeight low W cs
    (fun x hx => of_decide_eq_true (List.all_eq_true.mp opts x (mem x hx)))
  rw [edges_attached, len] at small
  have e : (cs.map (countBits b.length)).sum ≤ 40 - edges_ b - d := by omega
  have he := Nat.mul_le_mul_right edgeWeight e
  have hf := Nat.mul_le_mul_right extraWeight bound
  have hl := of_decide_eq_true last
  rw [len] at lower
  omega

private theorem complementaryPenalty (f : Nat → Bool) (cs : List Nat) :
    (cs.map (penalty f)).sum + (cs.map (penalty (fun x => !(f x)))).sum = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases eq : f c <;> simp [penalty, eq] at ih ⊢ <;> omega

private theorem zeroPenalty (cs : List Nat) :
    (cs.map (penalty (fun _ => false))).sum ≤ 0 := by
  induction cs with
  | nil => exact Nat.le_refl 0
  | cons c cs ih =>
    change 0 + (cs.map (penalty (fun _ => false))).sum ≤ 0
    rwa [Nat.zero_add]

private theorem all_of_penalty_ge (f : Nat → Bool) : ∀ cs : List Nat,
    cs.length ≤ (cs.map (penalty f)).sum → ∀ x ∈ cs, f x = true
  | [], _, _, hx => by simp at hx
  | c :: cs, h, x, hx => by
    have hle : ∀ l : List Nat, (l.map (penalty f)).sum ≤ l.length := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih => cases eq : f a <;> simp [penalty, eq] at ih ⊢ <;> omega
    have hcs := hle cs
    simp only [List.length_cons, List.map_cons, List.sum_cons] at h
    have hfc : f c = true := by
      cases eq : f c
      · simp [penalty, eq] at h; omega
      · rfl
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hfc
    · have htail : cs.length ≤ (cs.map (penalty f)).sum := by
        simp [penalty, hfc] at h; omega
      exact all_of_penalty_ge f cs htail x hx'

private theorem viaDual41 (b cs : List Nat) (d edgeWeight low : Nat) (W : List WeightedRow)
    (ext : Extension 6 d b cs)
    (check : dualCheckSimple 40 b d edgeWeight low W = true) :
    41 ≤ edges_ (attach cs b) := by
  by_contra! small
  obtain ⟨len, mem, good, _⟩ := ext
  obtain ⟨both, last⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨valid, opts⟩ := Bool.and_eq_true_iff.mp both
  have upper := rowScore_le b cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  have lower := rowScore_ge b (fun _ => false) edgeWeight 0 low W cs (fun x hx => by
    have hx' := of_decide_eq_true (List.all_eq_true.mp opts x (mem x hx))
    simp only [Nat.mul_zero, Nat.add_zero]
    exact hx')
  simp only [Nat.mul_zero, Nat.add_zero] at lower
  rw [edges_attached, len] at small
  have e : (cs.map (countBits b.length)).sum ≤ 40 - edges_ b - d := by omega
  have he := Nat.mul_le_mul_right edgeWeight e
  have hl := of_decide_eq_true last
  rw [len] at lower
  omega

private def b3_0w : List WeightedRow := [((2448,4),3),((1608,4),3),((3096,4),3),((4484,4),3),((204,4),3),((1570,4),3),((306,4),3),((4614,4),3),((30,4),3),((4673,4),3),((2241,4),3),((3105,4),3),((4385,4),3)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b3_0_40_cert : dualCheck40 b3_0 3 (fun _ => false) 0 3 0 24 b3_0w = true := by decide +kernel
private theorem b3_0_40_ok (cs : List Nat) (h : Extension 6 3 b3_0 cs) : 40 ≤ edges_ (attach cs b3_0) :=
  viaDual40 b3_0 cs 3 h (fun _ => false) 0 3 0 24 b3_0w b3_0_40_cert (zeroPenalty cs)

private def b4_0w0 : List WeightedRow := [((1224,4),2),((1576,4),6),((2244,4),2),((2340,4),2),((108,4),2),((786,4),2),((1170,4),4),((1546,4),6),((2310,4),2),((142,4),2),((801,4),2),((1121,4),4),((1553,4),2),((2321,4),2)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_0_40_cert0 : dualCheck40 b4_0 4 (fun x => x &&& 2048 == 0) 2 2 8 22 b4_0w0 = true := by decide +kernel
private def b4_0w1 : List WeightedRow := [((1224,4),62),((1576,4),59),((1128,4),2),((2244,4),42),((2340,4),49),((804,4),22),((2148,4),4),((204,4),2),((556,4),2),((108,4),61),((1554,4),2),((2322,4),6),((786,4),59),((2194,4),66),((1546,4),2),((1162,4),2),((2310,4),59),((526,4),59),((142,4),81),((2241,4),44),((2337,4),6),((801,4),64),((2145,4),49),((1121,4),17),((1553,4),59),((2321,4),59),((785,4),4),((2193,4),4),((1169,4),77)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_0_40_cert1 : dualCheck40 b4_0 4 (fun x => !(x &&& 2048 == 0)) 1 62 51 503 b4_0w1 = true := by decide +kernel
private theorem b4_0_40_ok (cs : List Nat) (h : Extension 6 4 b4_0 cs) : 40 ≤ edges_ (attach cs b4_0) := by
  by_cases yes : (cs.map (penalty (fun x => x &&& 2048 == 0))).sum ≤ 2
  · exact viaDual40 b4_0 cs 4 h (fun x => x &&& 2048 == 0) 2 2 8 22 b4_0w0 b4_0_40_cert0 yes
  · apply viaDual40 b4_0 cs 4 h (fun x => !(x &&& 2048 == 0)) 1 62 51 503 b4_0w1 b4_0_40_cert1
    have cp := complementaryPenalty (fun x => x &&& 2048 == 0) cs
    rw [h.1] at cp
    omega

private def b4_1w : List WeightedRow := [((2240,3),7),((272,2),22),((144,2),18),((200,3),20),((1224,4),40),((1576,4),39),((1128,4),11),((260,2),18),((2340,4),16),((804,4),27),((2148,4),38),((76,3),20),((556,4),6),((108,4),40),((1554,4),15),((786,4),30),((2194,4),55),((1170,4),16),((1546,4),18),((1162,4),38),((2310,4),55),((14,3),7),((526,4),42),((2241,4),42),((1217,4),6),((2337,4),10),((801,4),27),((2145,4),23),((1121,4),39),((1553,4),27),((2321,4),30),((785,4),18),((1169,4),27)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_1_40_cert : dualCheck40 b4_1 4 (fun _ => false) 0 71 0 505 b4_1w = true := by decide +kernel
private theorem b4_1_40_ok (cs : List Nat) (h : Extension 6 4 b4_1 cs) : 40 ≤ edges_ (attach cs b4_1) :=
  viaDual40 b4_1 cs 4 h (fun _ => false) 0 71 0 505 b4_1w b4_1_40_cert (zeroPenalty cs)

private def b4_6w : List WeightedRow := [((2192,3),2),((584,3),2),((840,4),2),((104,3),2),((788,4),3),((148,3),2),((1172,4),2),((1548,4),3),((2370,4),3),((2210,4),3),((1066,4),2),((106,4),2),((1158,4),3),((270,4),3),((833,4),2),((1185,4),3),((2145,4),3),((1553,4),3),((2321,4),3),((2193,4),2)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_6_40_cert : dualCheck40 b4_6 4 (fun _ => false) 0 4 0 28 b4_6w = true := by decide +kernel
private theorem b4_6_40_ok (cs : List Nat) (h : Extension 6 4 b4_6 cs) : 40 ≤ edges_ (attach cs b4_6) :=
  viaDual40 b4_6 cs 4 h (fun _ => false) 0 4 0 28 b4_6w b4_6_40_cert (zeroPenalty cs)

private def b4_2_41_w : List WeightedRow := [((800,3),1),((1224,4),3),((1576,4),5),((2244,4),3),((2340,4),5),((204,4),1),((108,4),4),((786,4),4),((2194,4),2),((1170,4),2),((1546,4),5),((2310,4),5),((142,4),4),((1217,4),2),((801,4),3),((2145,4),2),((1121,4),2),((1553,4),3),((2321,4),3),((785,4),1),((2193,4),2)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_2_41_cert : dualCheckSimple 40 b4_2 4 4 31 b4_2_41_w = true := by decide +kernel
private def b4_3_41_w : List WeightedRow := [((1224,4),3),((1576,4),2),((804,4),3),((2148,4),2),((108,4),3),((786,4),3),((146,3),2),((2194,4),3),((138,3),3),((2310,4),3),((14,3),2),((526,4),3),((2241,4),2),((2337,4),1),((1121,4),5),((1553,4),2),((2321,4),3),((785,4),1),((1169,4),3)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_3_41_cert : dualCheckSimple 40 b4_3 4 3 25 b4_3_41_w = true := by decide +kernel
private def b4_4_41_w : List WeightedRow := [((1216,3),1),((1544,3),1),((808,4),1),((2244,4),1),((108,4),1),((786,4),1),((146,3),1),((2310,4),1),((14,3),1),((2337,4),1),((1121,4),1),((1553,4),1),((2193,4),1)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_4_41_cert : dualCheckSimple 40 b4_4 4 1 8 b4_4_41_w = true := by decide +kernel
private def b4_5_41_w : List WeightedRow := [((784,3),3),((144,2),4),((840,4),9),((164,3),1),((2212,4),5),((1188,4),5),((2148,4),2),((1068,4),2),((108,4),9),((1554,4),1),((2322,4),4),((786,4),4),((1546,4),4),((778,4),1),((2182,4),4),((1158,4),1),((1038,4),3),((2369,4),4),((833,4),1),((2209,4),1),((1185,4),4),((2145,4),3),((1553,4),4),((2321,4),1),((785,4),4)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_5_41_cert : dualCheckSimple 40 b4_5 4 8 53 b4_5_41_w = true := by decide +kernel
private def b4_7_41_w : List WeightedRow := [((2368,3),1),((840,4),1),((788,4),1),((1172,4),1),((1548,4),1),((2210,4),1),((1186,4),1),((106,4),1),((14,3),1),((2145,4),1),((785,4),1),((2193,4),1)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_7_41_cert : dualCheckSimple 40 b4_7 4 0 4 b4_7_41_w = true := by decide +kernel
private def b4_8_41_w : List WeightedRow := [((792,4),1),((1176,4),1),((836,4),1),((1188,4),1),((1548,4),1),((2370,4),1),((2210,4),1),((102,4),1),((270,4),1),((142,4),1),((833,4),1),((1185,4),1),((2145,4),1),((1553,4),1),((2321,4),1),((2193,4),1)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_8_41_cert : dualCheckSimple 40 b4_8 4 1 8 b4_8_41_w = true := by decide +kernel
private def b4_9_41_w : List WeightedRow := [((840,4),1),((1064,3),1),((788,4),1),((1172,4),1),((1548,4),1),((2370,4),1),((2210,4),1),((106,4),1),((134,3),1),((270,4),1),((833,4),1),((1185,4),1),((2145,4),1),((1553,4),1),((2193,4),1)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_9_41_cert : dualCheckSimple 40 b4_9 4 1 8 b4_9_41_w = true := by decide +kernel
private def b4_10_41_w : List WeightedRow := [((1232,4),1),((808,4),1),((1560,4),1),((2244,4),1),((778,4),1),((2310,4),1),((86,4),1),((30,4),1),((2241,4),1),((1569,4),1),((2337,4),1),((1185,4),1)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_10_41_cert : dualCheckSimple 40 b4_10 4 0 4 b4_10_41_w = true := by decide +kernel
private def b4_11_41_w : List WeightedRow := [((1328,4),1),((1544,3),1),((1176,4),1),((2308,3),1),((404,4),1),((204,4),1),((2594,4),1),((50,3),1),((586,4),1),((2118,4),1),((30,4),1),((1409,4),1),((2625,4),1),((193,3),1),((1569,4),1),((2337,4),1)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_11_41_cert : dualCheckSimple 40 b4_11 4 2 12 b4_11_41_w = true := by decide +kernel

/- Fast complete enumerator for sorted 40-edge extensions of b3_0, b4_0, b4_1, b4_6. -/

private def activeInds (k d : Nat) (b : List Nat) : List (Nat × Nat) :=
  (inds b).filter (fun p => decide (k ≤ p.2 + d))

private def inds4 (b : List Nat) : List (Nat × Nat) :=
  (inds b).filter (fun p => p.2 == 4)

private def isStrictSorted : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => decide (x < y) && isStrictSorted (y :: rest)

private def poolOk (k d : Nat) (b pool : List Nat) : Bool :=
  isStrictSorted pool &&
  (usable k d b).all (fun x => decide (x ∈ pool)) &&
  pool.all (fun x => decide (countBits b.length x ≤ 4))

private def poolOk4 (k d : Nat) (b pool : List Nat) : Bool :=
  isStrictSorted pool &&
  ((usable k d b).filter (fun x => countBits b.length x == 4)).all (fun x => decide (x ∈ pool)) &&
  (usable k d b).all (fun x => decide (countBits b.length x ≤ 4)) &&
  pool.all (fun x => decide (countBits b.length x ≤ 4))

private theorem strictSorted_of_bool : ∀ l : List Nat, isStrictSorted l = true → l.Pairwise (· < ·)
  | [], _ => .nil
  | [_], _ => by simp
  | x :: y :: rest, h => by
    obtain ⟨hxy, hrest⟩ := Bool.and_eq_true_iff.mp h
    have ih := strictSorted_of_bool (y :: rest) hrest
    refine List.pairwise_cons.mpr ⟨?_, ih⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz'
    · exact of_decide_eq_true hxy
    · exact Nat.lt_trans (of_decide_eq_true hxy) ((List.pairwise_cons.mp ih).1 z hz')

private theorem okContacts_sublist {k : Nat} {isets : List (Nat × Nat)} {u v : List Nat}
    (hsub : u.Sublist v) (hv : okContacts k isets v = true) : okContacts k isets u = true := by
  rw [okContacts, List.all_eq_true] at hv ⊢
  intro p hp
  have h1 := of_decide_eq_true (hv p hp)
  have h2 := (hsub.filter (fun x => x &&& p.1 == 0)).length_le
  exact decide_eq_true (by omega)

private theorem okContacts_perm {k : Nat} {isets : List (Nat × Nat)} {u v : List Nat}
    (hp : u.Perm v) : okContacts k isets u = okContacts k isets v := by
  have h1 (p : Nat × Nat) :
      (u.filter fun x => x &&& p.1 == 0).length = (v.filter fun x => x &&& p.1 == 0).length :=
    (hp.filter _).length_eq
  simp [okContacts, h1]

private theorem okContacts_filter_isets {k : Nat} {isets : List (Nat × Nat)} {p : Nat × Nat → Bool}
    {cs : List Nat} (h : okContacts k isets cs = true) : okContacts k (isets.filter p) cs = true := by
  rw [okContacts, List.all_eq_true] at h ⊢
  intro q hq
  exact h q (List.mem_of_mem_filter hq)

private def enumGo (n : Nat) (is4 : List (Nat × Nat))
    (rec : Nat → List Nat → List Nat → List (List Nat))
    (d rem : Nat) (acc : List Nat) : List Nat → List (List Nat)
  | [] => []
  | x :: xs =>
    let w := countBits n x
    let take :=
      if w ≤ rem ∧ rem - w ≤ 4 * d ∧ okContacts 6 is4 (x :: acc) then
        let pool' := (x :: xs).filter (fun y => okContacts 6 is4 (y :: x :: acc))
        rec (rem - w) (x :: acc) pool'
      else []
    take ++ enumGo n is4 rec d rem acc xs

private def enumAux (n : Nat) (is4 isAll : List (Nat × Nat)) :
    Nat → Nat → List Nat → List Nat → List (List Nat)
  | 0, rem, acc, _ =>
    if rem = 0 ∧ okContacts 6 isAll acc.reverse then [acc.reverse] else []
  | d + 1, rem, acc, pool =>
    if rem > 4 * (d + 1) then []
    else enumGo n is4 (enumAux n is4 isAll d) d rem acc pool

private theorem sum_le_four_mul {n : Nat} : ∀ cs : List Nat,
    (∀ x ∈ cs, countBits n x ≤ 4) → (cs.map (countBits n)).sum ≤ 4 * cs.length
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := sum_le_four_mul xs (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

private theorem all_eq_four_of_sum {n : Nat} : ∀ cs : List Nat,
    (∀ x ∈ cs, countBits n x ≤ 4) → (cs.map (countBits n)).sum = 4 * cs.length →
    ∀ x ∈ cs, countBits n x = 4
  | [], _, _, _, hx => by simp at hx
  | a :: xs, hmax, hsum, x, hx => by
    have ha := hmax a (by simp)
    have hxs := sum_le_four_mul xs (fun y hy => hmax y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    rcases List.mem_cons.mp hx with rfl | hx'
    · omega
    · exact all_eq_four_of_sum xs (fun y hy => hmax y (by simp [hy])) (by omega) x hx'

private theorem perm_cons_rev_append (x : Nat) (acc : List Nat) :
    (x :: acc).Perm (acc.reverse ++ [x]) :=
  (List.perm_append_singleton x acc).symm.trans ((List.reverse_perm acc).symm.append_right [x])

private theorem perm_cons_cons_rev_append (y x : Nat) (acc : List Nat) :
    (y :: x :: acc).Perm (acc.reverse ++ [x, y]) := by
  have h1 : (y :: x :: acc).Perm ((x :: acc) ++ [y]) := (List.perm_append_singleton y (x :: acc)).symm
  have h2 : ((x :: acc) ++ [y]).Perm ((acc.reverse ++ [x]) ++ [y]) :=
    (perm_cons_rev_append x acc).append_right [y]
  simpa [List.append_assoc] using h1.trans h2

private theorem enumAux_complete (n : Nat) (is4 isAll : List (Nat × Nat)) :
    ∀ (d rem : Nat) (acc pool cs : List Nat),
      cs.length = d →
      (cs.map (countBits n)).sum = rem →
      (∀ x ∈ cs, countBits n x ≤ 4) →
      cs.Pairwise (· ≤ ·) →
      pool.Pairwise (· < ·) →
      (∀ x ∈ cs, x ∈ pool) →
      okContacts 6 is4 (acc.reverse ++ cs) = true →
      okContacts 6 isAll (acc.reverse ++ cs) = true →
      acc.reverse ++ cs ∈ enumAux n is4 isAll d rem acc pool
  | 0, rem, acc, pool, cs, hlen, hsum, _, _, _, _, _, hokAll => by
    cases cs with
    | nil =>
      simp only [List.map_nil, List.sum_nil] at hsum
      subst hsum
      simp only [List.append_nil] at hokAll ⊢
      simp [enumAux, hokAll]
    | cons _ _ => simp at hlen
  | d + 1, rem, acc, pool, cs, hlen, hsum, hmax, hsorted, hpsort, hmem, hok4, hokAll => by
    have hrem_le : rem ≤ 4 * (d + 1) := by
      rw [← hsum, ← hlen]
      exact sum_le_four_mul cs hmax
    simp only [enumAux, show ¬ (rem > 4 * (d + 1)) by omega, ↓reduceIte]
    cases cs with
    | nil => simp at hlen
    | cons c cs' =>
      have hlen' : cs'.length = d := by simpa using hlen
      have hcs'_max : ∀ x ∈ cs', countBits n x ≤ 4 := fun x hx => hmax x (by simp [hx])
      have hcs'_le : ∀ x ∈ cs', c ≤ x := (List.pairwise_cons.mp hsorted).1
      have hcs'_sort : cs'.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hsorted).2
      have hsum' : (cs'.map (countBits n)).sum = rem - countBits n c := by
        simp only [List.map_cons, List.sum_cons] at hsum; omega
      have hw_le : countBits n c ≤ rem := by
        simp only [List.map_cons, List.sum_cons] at hsum; omega
      have hrem'_le : rem - countBits n c ≤ 4 * d := by
        rw [← hsum', ← hlen']
        exact sum_le_four_mul cs' hcs'_max
      induction pool with
      | nil =>
        have := hmem c (by simp)
        simp at this
      | cons x xs ih =>
        have hx_lt : ∀ y ∈ xs, x < y := (List.pairwise_cons.mp hpsort).1
        have hxs_sort : xs.Pairwise (· < ·) := (List.pairwise_cons.mp hpsort).2
        by_cases hcx : c = x
        · subst hcx
          simp only [enumGo, List.mem_append]
          left
          have hok_x : okContacts 6 is4 (c :: acc) = true := by
            rw [okContacts_perm (perm_cons_rev_append c acc)]
            apply okContacts_sublist _ hok4
            exact List.Sublist.append_left (List.Sublist.cons_cons c (List.nil_sublist cs')) acc.reverse
          have hcond : countBits n c ≤ rem ∧ rem - countBits n c ≤ 4 * d ∧ okContacts 6 is4 (c :: acc) = true :=
            ⟨hw_le, hrem'_le, hok_x⟩
          simp only [hcond, and_self, ↓reduceIte]
          have hpool'_sort : ((c :: xs).filter (fun y => okContacts 6 is4 (y :: c :: acc))).Pairwise (· < ·) :=
            hpsort.filter _
          have hmem' : ∀ y ∈ cs', y ∈ (c :: xs).filter (fun y => okContacts 6 is4 (y :: c :: acc)) := by
            intro y hy
            rw [List.mem_filter]
            refine ⟨hmem y (by simp [hy]), ?_⟩
            rw [okContacts_perm (perm_cons_cons_rev_append y c acc)]
            apply okContacts_sublist _ hok4
            have hy_sub : [y].Sublist cs' := List.singleton_sublist.mpr hy
            exact List.Sublist.append_left (List.Sublist.cons_cons c hy_sub) acc.reverse
          have hgoal := enumAux_complete n is4 isAll d (rem - countBits n c) (c :: acc)
            ((c :: xs).filter (fun y => okContacts 6 is4 (y :: c :: acc))) cs'
            hlen' hsum' hcs'_max hcs'_sort hpool'_sort hmem'
            (by simpa [List.reverse_cons, List.append_assoc] using hok4)
            (by simpa [List.reverse_cons, List.append_assoc] using hokAll)
          simpa [List.reverse_cons, List.append_assoc] using hgoal
        · simp only [enumGo, List.mem_append]
          right
          apply ih hxs_sort
          intro y hy
          have hym := hmem y hy
          rcases List.mem_cons.mp hym with hyx | hyxs
          · rcases List.mem_cons.mp hy with hyc | hy'
            · exact (hcx (hyc.symm.trans hyx)).elim
            · have hcm : c ∈ xs := (List.mem_cons.mp (hmem c (by simp))).resolve_left hcx
              have hlt := hx_lt c hcm
              have hle := hcs'_le y hy'
              omega
          · exact hyxs

private theorem classify_via_enum {d : Nat} (b pool : List Nat) (sols : List (List Nat))
    (cs : List Nat) (hcs : Extension 6 d b cs) (he40 : edges_ (attach cs b) = 40)
    (hsort : isStrictSorted pool = true)
    (hcs_in_pool : ∀ x ∈ cs, x ∈ pool)
    (hpool_max : pool.all (fun x => decide (countBits b.length x ≤ 4)) = true)
    (henum : enumAux b.length (inds4 b) (activeInds 6 d b) d (40 - edges_ b - d) [] pool = sols) :
    cs ∈ sols := by
  obtain ⟨hlen, _, hok, hpw⟩ := hcs
  rw [edges_attached, hlen] at he40
  have hsum : (cs.map (countBits b.length)).sum = 40 - edges_ b - d := by omega
  have hcs_max : ∀ x ∈ cs, countBits b.length x ≤ 4 := fun x hx =>
    of_decide_eq_true (List.all_eq_true.mp hpool_max x (hcs_in_pool x hx))
  have hok4 : okContacts 6 (inds4 b) ([] ++ cs) = true := by
    unfold inds4; simpa using okContacts_filter_isets (p := fun p => p.2 == 4) hok
  have hokAll : okContacts 6 (activeInds 6 d b) ([] ++ cs) = true := by
    unfold activeInds; simpa using okContacts_filter_isets (p := fun p => decide (6 ≤ p.2 + d)) hok
  have hres := enumAux_complete b.length (inds4 b) (activeInds 6 d b) d (40 - edges_ b - d) [] pool cs
    hlen hsum hcs_max hpw (strictSorted_of_bool pool hsort) hcs_in_pool hok4 hokAll
  rw [henum] at hres
  simpa using hres

private theorem classify_via_poolOk {d : Nat} (b pool : List Nat) (sols : List (List Nat))
    (cs : List Nat) (hcs : Extension 6 d b cs) (he40 : edges_ (attach cs b) = 40)
    (hpool : poolOk 6 d b pool = true)
    (henum : enumAux b.length (inds4 b) (activeInds 6 d b) d (40 - edges_ b - d) [] pool = sols) :
    cs ∈ sols := by
  obtain ⟨h12, hmax⟩ := Bool.and_eq_true_iff.mp hpool
  obtain ⟨hsort, hsub⟩ := Bool.and_eq_true_iff.mp h12
  exact classify_via_enum b pool sols cs hcs he40 hsort
    (fun x hx => of_decide_eq_true (List.all_eq_true.mp hsub x (hcs.2.1 x hx))) hmax henum

private theorem classify_via_poolOk4 (b pool : List Nat) (sols : List (List Nat))
    (cs : List Nat) (hcs : Extension 6 4 b cs) (he40 : edges_ (attach cs b) = 40)
    (he20 : edges_ b = 20)
    (hpool : poolOk4 6 4 b pool = true)
    (henum : enumAux b.length (inds4 b) (activeInds 6 4 b) 4 (40 - edges_ b - 4) [] pool = sols) :
    cs ∈ sols := by
  obtain ⟨h123, hmax⟩ := Bool.and_eq_true_iff.mp hpool
  obtain ⟨h12, husable_max⟩ := Bool.and_eq_true_iff.mp h123
  obtain ⟨hsort, hsub4⟩ := Bool.and_eq_true_iff.mp h12
  have hcs_max : ∀ x ∈ cs, countBits b.length x ≤ 4 := fun x hx =>
    of_decide_eq_true (List.all_eq_true.mp husable_max x (hcs.2.1 x hx))
  have hsum16 : (cs.map (countBits b.length)).sum = 4 * cs.length := by
    rw [edges_attached, hcs.1, he20] at he40
    rw [hcs.1]; omega
  have hall4 := all_eq_four_of_sum cs hcs_max hsum16
  have hin : ∀ x ∈ cs, x ∈ pool := fun x hx => by
    have hmem4 : x ∈ (usable 6 4 b).filter (fun y => countBits b.length y == 4) :=
      List.mem_filter.mpr ⟨hcs.2.1 x hx, by simp [hall4 x hx]⟩
    exact of_decide_eq_true (List.all_eq_true.mp hsub4 x hmem4)
  exact classify_via_enum b pool sols cs hcs he40 hsort hin hmax henum


private def pool_b3_0 : List Nat := [6, 10, 12, 14, 18, 20, 22, 24, 26, 28, 30, 33, 34, 48, 50, 65, 68, 72, 76, 129, 132, 136, 140, 144, 148, 152, 156, 192, 193, 196, 200, 204, 257, 258, 260, 262, 272, 274, 276, 278, 288, 289, 290, 304, 306, 384, 385, 388, 400, 404, 513, 514, 516, 518, 520, 522, 524, 526, 544, 545, 546, 576, 577, 580, 584, 588, 1025, 1026, 1032, 1034, 1040, 1042, 1048, 1050, 1056, 1057, 1058, 1072, 1074, 1088, 1089, 1096, 1536, 1537, 1538, 1544, 1546, 1568, 1569, 1570, 1600, 1601, 1608, 2049, 2056, 2064, 2072, 2080, 2081, 2096, 2112, 2113, 2120, 2176, 2177, 2184, 2192, 2200, 2240, 2241, 2248, 2304, 2305, 2320, 2336, 2337, 2352, 2432, 2433, 2448, 3072, 3073, 3080, 3088, 3096, 3104, 3105, 3120, 3136, 3137, 3144, 4097, 4098, 4100, 4102, 4128, 4129, 4130, 4160, 4161, 4164, 4224, 4225, 4228, 4288, 4289, 4292, 4352, 4353, 4354, 4356, 4358, 4384, 4385, 4386, 4480, 4481, 4484, 4608, 4609, 4610, 4612, 4614, 4640, 4641, 4642, 4672, 4673, 4676]
private def sols_b3_0 : List (List Nat) := []
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem pool_b3_0_ok : poolOk 6 3 b3_0 pool_b3_0 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private theorem enum_b3_0_ok : enumAux b3_0.length (inds4 b3_0) (activeInds 6 3 b3_0) 3 11 [] pool_b3_0 = sols_b3_0 := by decide +kernel

private def pool_b4_0 : List Nat := [108, 142, 204, 526, 556, 774, 785, 786, 801, 804, 1121, 1128, 1162, 1169, 1170, 1217, 1224, 1546, 1553, 1554, 1569, 1576, 2145, 2148, 2182, 2193, 2194, 2241, 2244, 2310, 2321, 2322, 2337, 2340]
private def sols_b4_0 : List (List Nat) := [[142, 804, 1553, 2241], [526, 801, 1169, 2244], [1121, 1546, 2194, 2340], [1170, 1576, 2145, 2310]]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem pool_b4_0_ok : poolOk4 6 4 b4_0 pool_b4_0 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private theorem enum_b4_0_ok : enumAux b4_0.length (inds4 b4_0) (activeInds 6 4 b4_0) 4 16 [] pool_b4_0 = sols_b4_0 := by decide +kernel

private def pool_b4_1 : List Nat := [14, 44, 76, 97, 100, 104, 108, 138, 145, 146, 193, 200, 262, 273, 274, 289, 292, 518, 522, 524, 526, 529, 530, 545, 548, 552, 556, 769, 770, 772, 774, 784, 785, 786, 800, 801, 804, 1034, 1041, 1042, 1057, 1064, 1089, 1096, 1120, 1121, 1128, 1153, 1154, 1160, 1162, 1168, 1169, 1170, 1216, 1217, 1224, 1537, 1538, 1544, 1546, 1552, 1553, 1554, 1568, 1569, 1576, 2054, 2065, 2066, 2081, 2084, 2113, 2116, 2144, 2145, 2148, 2177, 2178, 2192, 2193, 2194, 2240, 2241, 2305, 2306, 2308, 2310, 2320, 2321, 2322, 2336, 2337, 2340]
private def sols_b4_1 : List (List Nat) := [[1034, 1569, 2145, 2322], [1057, 1546, 2194, 2340], [1154, 1569, 2145, 2310], [1162, 1569, 2145, 2306], [1170, 1568, 2145, 2310], [1546, 1569, 2066, 2148], [1546, 1569, 2084, 2194], [1546, 1569, 2144, 2322]]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem pool_b4_1_ok : poolOk 6 4 b4_1 pool_b4_1 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private theorem enum_b4_1_ok : enumAux b4_1.length (inds4 b4_1) (activeInds 6 4 b4_1) 4 15 [] pool_b4_1 = sols_b4_1 := by decide +kernel

private def pool_b4_6 : List Nat := [262, 785, 1038, 1057, 1186, 1537, 2306, 2369]
private def sols_b4_6 : List (List Nat) := [[262, 1186, 1537, 2369], [785, 1038, 1057, 2306]]
private def b4_6_excl_w : List WeightedRow := [((2192,3),3),((584,3),3),((840,4),6),((104,3),3),((788,4),9),((148,3),3),((1172,4),6),((1548,4),9),((2370,4),9),((2210,4),9),((1186,4),5),((1066,4),1),((106,4),6),((1158,4),2),((1038,4),7),((270,4),9),((2369,4),7),((833,4),1),((1185,4),9),((2145,4),9),((1553,4),9),((2321,4),2),((785,4),5),((2193,4),6)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_6_excl_cert :
    dualCheck41Pen b4_6 4 (fun x => decide (x ∈ pool_b4_6)) 3 9 3 72 b4_6_excl_w = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem pool_b4_6_sorted : isStrictSorted pool_b4_6 = true ∧ pool_b4_6.all (fun x => decide (countBits b4_6.length x ≤ 4)) = true := by
  decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private theorem enum_b4_6_ok : enumAux b4_6.length (inds4 b4_6) (activeInds 6 4 b4_6) 4 14 [] pool_b4_6 = sols_b4_6 := by decide +kernel


/- 17-vertex dual check proving no 3 independent sets of total size <= 9 satisfy okContacts 7. -/

private def rowCapacity7 (W : List WeightedRow) : Nat :=
  (W.map fun w => (6 - w.1.2) * w.2).sum

private def dualCheck17 (g : List Nat) (edgeWeight low : Nat) (W : List WeightedRow) : Bool :=
  let is := inds g
  W.all (fun w => decide (w.1 ∈ is)) &&
  is.all (fun p => decide (low ≤ countBits g.length p.1 * edgeWeight + rowScore W p.1)) &&
  decide (9 * edgeWeight + rowCapacity7 W < 3 * low)

private theorem rowScore_le7 (g cs : List Nat) (W : List WeightedRow)
    (valid : ∀ w ∈ W, w.1 ∈ inds g) (good : okContacts 7 (inds g) cs = true) :
    (cs.map (rowScore W)).sum ≤ rowCapacity7 W := by
  induction W with
  | nil =>
    have h : rowScore [] = fun _ => 0 := rfl
    simp [h, rowCapacity7]
  | cons w W ih =>
    have sub := ih (fun t ht => valid t (.tail _ ht))
    have hm := of_decide_eq_true (List.all_eq_true.mp good w.1 (valid w (.head _)))
    have lecap : (cs.filter (fun x => x &&& w.1.1 == 0)).length ≤ 6 - w.1.2 := by omega
    have lh := Nat.mul_le_mul_right w.2 lecap
    rw [rowScore_cons]
    change _ ≤ (6 - w.1.2) * w.2 + rowCapacity7 W
    omega

private theorem viaDual17 (g cs : List Nat) (edgeWeight low : Nat) (W : List WeightedRow)
    (hlen : cs.length = 3)
    (hmem : ∀ x ∈ cs, ∃ p ∈ inds g, p.1 = x)
    (hgood : okContacts 7 (inds g) cs = true)
    (hsum : (cs.map (countBits g.length)).sum ≤ 9)
    (check : dualCheck17 g edgeWeight low W = true) : False := by
  unfold dualCheck17 at check
  dsimp only at check
  obtain ⟨both, last⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨valid, opts⟩ := Bool.and_eq_true_iff.mp both
  have upper := rowScore_le7 g cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) hgood
  have lower := rowScore_ge g (fun _ => false) edgeWeight 0 low W cs (fun x hx => by
    obtain ⟨p, hp, rfl⟩ := hmem x hx
    have hx' := of_decide_eq_true (List.all_eq_true.mp opts p hp)
    simp only [Nat.mul_zero, Nat.add_zero]
    exact hx')
  simp only [Nat.mul_zero, Nat.add_zero] at lower
  have he := Nat.mul_le_mul_right edgeWeight hsum
  have hl := of_decide_eq_true last
  rw [hlen] at lower
  omega


private abbrev g17_rep0 : List Nat := [15, 1136, 3216, 3106, 2241, 7, 24, 130, 145, 3, 2, 6, 3, 2, 2, 1, 0]
private def w17_rep0 : List WeightedRow := [((50448,5),1),((17808,5),2),((25168,5),2),((49488,5),1),((16848,5),2),((71816,5),1),((74888,5),2),((6536,5),1),((3464,5),2),((73928,5),2),((9368,5),2),((8408,5),2),((39172,5),2),((70212,5),1),((37444,5),1),((70180,5),2),((37412,5),2),((6412,5),2),((4428,5),2),((348,5),2),((25634,5),1),((68642,5),2),((35874,5),2),((74274,5),2),((25122,5),1),((49682,5),2),((25106,5),2),((9242,5),2),((67622,5),2),((34854,5),2),((33302,5),2),((67598,5),2),((30,4),2),((50433,5),1),((25729,5),1),((68737,5),1),((6529,5),2),((3457,5),1),((70209,5),1),((37441,5),1),((49473,5),1),((24769,5),1),((69825,5),2),((4545,5),1),((71713,5),1),((38945,5),1),((50209,5),2),((74785,5),1),((49697,5),1),((74273,5),1),((25121,5),2)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 15000000 in
private theorem cert17_rep0 : dualCheck17 g17_rep0 9 55 w17_rep0 = true := by decide +kernel

private abbrev g17_rep1 : List Nat := [15, 8272, 6276, 4290, 2322, 7, 24, 146, 145, 3, 2, 6, 3, 2, 2, 1, 0]
private def w17_rep1 : List WeightedRow := [((36112,5),1),((3472,5),1),((38960,5),1),((50224,5),2),((35888,5),1),((49736,5),2),((25160,5),1),((37448,5),1),((49432,5),2),((37144,5),1),((74308,5),1),((70212,5),1),((73924,5),2),((6420,5),1),((2452,5),2),((8780,5),1),((4428,5),1),((460,5),2),((25730,5),1),((74786,5),1),((68642,5),1),((74274,5),2),((70178,5),1),((17458,5),1),((3122,5),1),((24714,5),1),((71686,5),2),((67718,5),1),((8718,5),2),((4126,5),2),((158,5),1),((36097,5),2),((25729,5),1),((17793,5),1),((74305,5),1),((49473,5),1),((37185,5),2),((73921,5),1),((71713,5),1),((74785,5),1),((68641,5),2),((49697,5),1),((74273,5),1),((37409,5),2)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 15000000 in
private theorem cert17_rep1 : dualCheck17 g17_rep1 7 41 w17_rep1 = true := by decide +kernel

private def sw17_0 : List Nat := []
set_option maxRecDepth 16000 in
private theorem rel17_0 : relabel sw17_0 (attach [142, 804, 1553, 2241] b4_0) = g17_rep0 := by decide +kernel
private def sw17_1 : List Nat := [1, 3, 11, 10, 9, 8, 7, 6, 5, 10, 9, 8, 7, 6, 13, 12, 11, 10, 9, 8, 7, 13, 12, 11, 10, 9, 8, 13, 12, 11, 10, 9, 10, 13, 12, 11, 13, 15]
set_option maxRecDepth 16000 in
private theorem rel17_1 : relabel sw17_1 (attach [526, 801, 1169, 2244] b4_0) = g17_rep0 := by decide +kernel
private def sw17_2 : List Nat := [3, 2, 3, 5, 9, 8, 7, 10, 9, 8, 10, 9, 14, 13, 12, 13, 15, 14]
set_option maxRecDepth 16000 in
private theorem rel17_2 : relabel sw17_2 (attach [1121, 1546, 2194, 2340] b4_0) = g17_rep0 := by decide +kernel
private def sw17_3 : List Nat := [1, 3, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 14, 13, 12, 11, 10, 9, 8, 7, 6, 15, 14, 13, 12, 11, 10, 9, 8, 7, 10, 9, 8, 15, 14, 13, 12, 11, 10, 9, 15, 14, 13, 12, 11, 10, 15, 14, 13, 12, 11, 15, 14, 13, 12, 15, 14, 13, 14, 15]
set_option maxRecDepth 16000 in
private theorem rel17_3 : relabel sw17_3 (attach [1170, 1576, 2145, 2310] b4_0) = g17_rep0 := by decide +kernel
private def sw17_4 : List Nat := []
set_option maxRecDepth 16000 in
private theorem rel17_4 : relabel sw17_4 (attach [1034, 1569, 2145, 2322] b4_1) = g17_rep1 := by decide +kernel
private def sw17_5 : List Nat := [10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 7, 6, 5, 4, 3, 2, 10, 9, 8, 7, 6, 5, 4, 3, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 7, 6, 5, 13, 12, 11, 10, 9, 8, 7, 6, 15, 14, 13, 12, 11, 10, 9, 8, 10, 9, 14, 13, 12, 11, 10, 13, 12, 11, 15, 14, 13, 14]
set_option maxRecDepth 16000 in
private theorem rel17_5 : relabel sw17_5 (attach [1057, 1546, 2194, 2340] b4_1) = g17_rep1 := by decide +kernel
private def sw17_6 : List Nat := [13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 2, 1, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 6, 5, 13, 12, 11, 10, 9, 8, 7, 9, 8, 10, 9, 15, 14, 13, 12, 15, 14, 15]
set_option maxRecDepth 16000 in
private theorem rel17_6 : relabel sw17_6 (attach [1154, 1569, 2145, 2310] b4_1) = g17_rep0 := by decide +kernel
private def sw17_7 : List Nat := [13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 5, 4, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 11, 10, 9, 8, 7, 6, 15, 14, 13, 12, 11, 10, 9, 8, 7, 8, 13, 12, 11, 10, 9, 14, 13, 12, 11, 10, 13, 12, 11, 15, 14, 13, 12, 15, 14, 13, 14, 15]
set_option maxRecDepth 16000 in
private theorem rel17_7 : relabel sw17_7 (attach [1162, 1569, 2145, 2306] b4_1) = g17_rep0 := by decide +kernel
private def sw17_8 : List Nat := [4, 3, 2, 1, 0, 7, 6, 5, 4, 3, 2, 1, 4, 3, 2, 6, 5, 4, 3, 7, 6, 5, 4, 10, 9, 8, 7, 6, 5, 9, 8, 7, 6, 13, 12, 11, 10, 9, 8, 7, 13, 12, 11, 10, 9, 8, 13, 12, 11, 10, 9, 13, 12, 11, 10, 11, 12, 14, 13, 15]
set_option maxRecDepth 16000 in
private theorem rel17_8 : relabel sw17_8 (attach [1170, 1568, 2145, 2310] b4_1) = g17_rep1 := by decide +kernel
private def sw17_9 : List Nat := [4, 3, 2, 1, 0, 5, 4, 3, 2, 1, 3, 2, 6, 5, 4, 3, 7, 6, 5, 4, 8, 7, 6, 5, 7, 6, 9, 8, 7, 10, 9, 8, 10, 9, 15, 14, 13, 12, 11, 14, 13, 15, 14]
set_option maxRecDepth 16000 in
private theorem rel17_9 : relabel sw17_9 (attach [1546, 1569, 2066, 2148] b4_1) = g17_rep0 := by decide +kernel
private def sw17_10 : List Nat := [4, 3, 2, 1, 0, 2, 1, 6, 5, 4, 3, 2, 7, 6, 5, 4, 3, 7, 6, 5, 4, 5, 14, 13, 12, 11, 10, 9, 8, 7, 14, 13, 12, 11, 10, 9, 8, 15, 14, 13, 12, 11, 10, 9, 12, 14, 13, 15]
set_option maxRecDepth 16000 in
private theorem rel17_10 : relabel sw17_10 (attach [1546, 1569, 2084, 2194] b4_1) = g17_rep0 := by decide +kernel
private def sw17_11 : List Nat := [2, 1, 2, 13, 12, 11, 10, 9, 8, 7, 6, 5, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 13, 12, 11, 10, 9, 8, 7, 13, 12, 11, 10, 9, 8, 14, 13, 12, 11, 10, 9, 15, 14, 13, 12, 11, 10, 13, 12, 11, 13, 12, 14, 13, 15]
set_option maxRecDepth 16000 in
private theorem rel17_11 : relabel sw17_11 (attach [1546, 1569, 2144, 2322] b4_1) = g17_rep1 := by decide +kernel
private def sw17_12 : List Nat := [7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 6, 5, 4, 3, 2, 1, 6, 5, 4, 3, 2, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 12, 11, 10, 9, 8, 7, 6, 5, 4, 10, 9, 8, 7, 6, 5, 12, 11, 10, 9, 8, 7, 6, 7, 12, 11, 10, 9, 8, 13, 12, 11, 10, 9, 12, 11, 10, 15, 14, 13, 12, 11]
set_option maxRecDepth 16000 in
private theorem rel17_12 : relabel sw17_12 (attach [262, 1186, 1537, 2369] b4_6) = g17_rep1 := by decide +kernel
private def sw17_13 : List Nat := [10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 9, 8, 7, 6, 5, 4, 3, 11, 10, 9, 8, 7, 6, 5, 4, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 12, 11, 10, 9, 8, 7, 6, 10, 9, 8, 7, 15, 14, 13, 12, 11, 10, 9, 8, 13, 12, 11, 10, 9, 11, 10, 13, 12, 11, 15]
set_option maxRecDepth 16000 in
private theorem rel17_13 : relabel sw17_13 (attach [785, 1038, 1057, 2306] b4_6) = g17_rep1 := by decide +kernel

private theorem countBits_bits_eq {n : Nat} : ∀ bs : List Bool, bs.length = n →
    countBits n (bits bs) = (bs.filter id).length
  | [], h => by subst h; rfl
  | b :: bs, h => by
    subst h
    simp only [List.length_cons, countBits, bits]
    have ih := countBits_bits_eq bs rfl
    cases b
    · simp only [Bool.toNat_false, Nat.add_zero, List.filter, id_eq,
        Nat.mul_mod_right, Nat.mul_div_right _ (by decide : 0 < 2)]
      omega
    · simp only [Bool.toNat_true, List.filter, id_eq, List.length_cons]
      have h1 : (2 * bits bs + 1) % 2 = 1 := by omega
      have h2 : (2 * bits bs + 1) / 2 = bits bs := by omega
      rw [h1, h2, ih]
      omega

private theorem kill_via_relabel (G : SimpleGraph (Fin 21)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 7)
    (N B : Finset (Fin 21)) (hNcard : N.card = 3) (hNind : Gᶜ.IsClique (N : Set (Fin 21)))
    (hdisjNB : ∀ x ∈ N, x ∉ B)
    (hsum9 : ∑ u ∈ N, (B.filter (G.Adj u)).card ≤ 9)
    (vs : List (Fin 21)) (hvs_nd : vs.Nodup) (hvs_cov : vs.toFinset = B)
    (g target : List Nat) (hvs_enc : encode G vs = g)
    (swaps : List Nat) (hrel : relabel swaps g = target)
    (ew low : Nat) (W : List WeightedRow) (hcert : dualCheck17 target ew low W = true) : False := by
  classical
  obtain ⟨vs', hperm, henc'⟩ := relabel_real G swaps vs
  rw [hvs_enc, hrel] at henc'
  have hvs'_nd : vs'.Nodup := hperm.nodup_iff.mpr hvs_nd
  have hvs'_cov : vs'.toFinset = B := by
    rw [← hvs_cov]
    ext x
    simp [hperm.mem_iff]
  let front3 := N.toList
  have hfr_nd : front3.Nodup := Finset.nodup_toList N
  have hfr_cov : front3.toFinset = N := by ext x; simp [front3]
  have hfr_len : front3.length = 3 := by rw [Finset.length_toList, hNcard]
  let cs3 : List Nat := front3.map (fun u => bits (vs'.map fun y => decide (G.Adj u y)))
  have hcs3_len : cs3.length = 3 := by simp [cs3, hfr_len]
  have hcs3_mem : ∀ x ∈ cs3, ∃ p ∈ inds target, p.1 = x := by
    intro x hx
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
    let S := vs'.toFinset.filter (G.Adj u)
    have hrow := inds_complete G vs' hvs'_nd S (Finset.filter_subset ..) (neighbors_small G ht _ u)
    rw [henc'] at hrow
    refine ⟨(mark vs' S, S.card), hrow, ?_⟩
    exact (row_mark G vs' u).symm
  have hcs3_ok : okContacts 7 (inds target) cs3 = true := by
    have hdisj_fv : ∀ x ∈ front3, ∀ y ∈ vs', x ≠ y := by
      intro x hx y hy hxy
      subst hxy
      exact hdisjNB x (hfr_cov ▸ List.mem_toFinset.mpr hx) (hvs'_cov ▸ List.mem_toFinset.mpr hy)
    have hnd_app : (front3 ++ vs').Nodup := List.nodup_append.mpr ⟨hfr_nd, hvs'_nd, hdisj_fv⟩
    have hsmall7 : Small G Finset.univ 7 := by
      intro I _ hI
      by_contra! hc
      exact (hi.mono hc) I ⟨hI, rfl⟩
    have hok := ok_contacts G Finset.univ 7 hsmall7 front3 vs' hnd_app (Finset.subset_univ _) (by simpa [hfr_cov] using hNind)
    rwa [henc'] at hok
  have hcs3_sum : (cs3.map (countBits target.length)).sum ≤ 9 := by
    rw [← henc', encode_length]
    have hmap : cs3.map (countBits vs'.length) = front3.map (fun u => (B.filter (G.Adj u)).card) := by
      simp only [cs3, List.map_map]
      apply List.map_congr_left
      intro u _
      simp only [Function.comp_apply]
      rw [countBits_bits_eq _ (List.length_map ..)]
      have hfilt : ((vs'.map fun y => decide (G.Adj u y)).filter id).length = sizeAt G vs' u := by
        clear * -
        induction vs' with
        | nil => rfl
        | cons y ys ih =>
          by_cases h : G.Adj u y <;> simp [sizeAt, h, ih]
      rw [hfilt, sizeAt_finset G hvs'_nd, hvs'_cov]
    rw [hmap]
    have hst := List.sum_toFinset (fun u => (B.filter (G.Adj u)).card) hfr_nd
    rw [hfr_cov] at hst
    rw [← hst]
    exact hsum9
  exact viaDual17 target cs3 ew low W hcs3_len hcs3_mem hcs3_ok hcs3_sum hcert

theorem no_deg3_21_52 (G : SimpleGraph (Fin 21)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 7) (hedges : G.edgeFinset.card = 52)
    (w : Fin 21) (hw : G.degree w = 3)
    (h14 : RamseyNumbers.IsGraphRamsey 14 3 5)
    (h9 : RamseyNumbers.IsGraphRamsey 9 3 4) : False := by
  classical
  let N : Finset (Fin 21) := G.neighborFinset w
  let B : Finset (Fin 21) := Gᶜ.neighborFinset w
  have hNcard : N.card = 3 := by simpa [N] using hw
  have hBcard : B.card = 17 := by
    have hc := G.degree_compl w
    rw [Fintype.card_fin] at hc
    change Gᶜ.degree w = 17
    omega
  have hNind : Gᶜ.IsClique (N : Set (Fin 21)) := by
    rw [G.coe_neighborFinset, G.isClique_compl]
    exact G.isIndepSet_neighborSet_of_triangleFree ht w
  have hdisjNB : ∀ x ∈ N, x ∉ B := fun x hxN hxB =>
    ((Gᶜ.mem_neighborFinset w x).mp hxB).2 ((G.mem_neighborFinset w x).mp hxN)
  have hdeg_split (u : Fin 21) (hu : u ∈ N) : (B.filter (G.Adj u)).card + 1 = G.degree u := by
    have hwu : G.Adj w u := (G.mem_neighborFinset w u).mp hu
    have heq : G.neighborFinset u = insert w (B.filter (G.Adj u)) := by
      ext x
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_filter, B,
        SimpleGraph.compl_adj]
      constructor
      · intro hux
        by_cases hxw : x = w
        · exact Or.inl hxw
        · refine Or.inr ⟨⟨Ne.symm hxw, ?_⟩, hux⟩
          intro hwx
          exact G.isIndepSet_neighborSet_of_triangleFree ht w hwu hwx hux.ne hux
      · rintro (rfl | ⟨_, hux⟩)
        · exact hwu.symm
        · exact hux
    have hw_not : w ∉ B.filter (G.Adj u) := by
      simp [B, SimpleGraph.mem_neighborFinset]
    rw [← G.card_neighborFinset_eq_degree u, heq, Finset.card_insert_of_notMem hw_not]
  have hsumA_ge : 9 ≤ ∑ u ∈ N, (B.filter (G.Adj u)).card := by
    by_contra! hlt
    let cov := N.biUnion (fun u => B.filter (G.Adj u))
    have hcov_le : cov.card ≤ 8 := (Finset.card_biUnion_le).trans (by omega)
    let U := B \ cov
    have hU_ge : 9 ≤ U.card := by
      have h1 : B.card - cov.card ≤ U.card := Finset.le_card_sdiff cov B
      omega
    obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset (α := Fin 9) (s := U) (by simpa using hU_ge)
    let K := G.comap f
    let emb : K ↪g G := SimpleGraph.Embedding.comap f G
    apply h9 K
    refine ⟨SimpleGraph.CliqueFree.comap emb.isContained ht, ?_⟩
    intro S hS
    let S' := S.map f
    have hS'card : S'.card = 4 := (Finset.card_map f).trans hS.card_eq
    have hS'U : ∀ x ∈ S', x ∈ U := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      exact hf ⟨i, rfl⟩
    have hS'ind : Gᶜ.IsClique (S' : Set (Fin 21)) := by
      intro x hx y hy hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
      exact (SimpleGraph.Embedding.complEquiv emb).map_adj_iff.mpr
        (hS.isClique hi hj (fun h => hne (congrArg f h)))
    have hdisj : Disjoint S' N := by
      refine Finset.disjoint_left.mpr fun x hxS hxN => ?_
      exact hdisjNB x hxN (Finset.mem_sdiff.mp (hS'U x hxS)).1
    have hcross : ∀ x ∈ S', ∀ u ∈ N, Gᶜ.Adj x u := by
      intro x hxS u huN
      refine ⟨fun h => Finset.disjoint_left.mp hdisj hxS (h ▸ huN), fun hadj => ?_⟩
      have hxU := Finset.mem_sdiff.mp (hS'U x hxS)
      exact hxU.2 (Finset.mem_biUnion.mpr ⟨u, huN, Finset.mem_filter.mpr ⟨hxU.1, hadj.symm⟩⟩)
    apply hi (S' ∪ N)
    refine ⟨?_, by rw [Finset.card_union_of_disjoint hdisj, hS'card, hNcard]⟩
    intro x hx y hy hne
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with hxS | hxN <;>
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hy) with hyS | hyN
    · exact hS'ind hxS hyS hne
    · exact hcross x hxS y hyN
    · exact (hcross y hyS x hxN).symm
    · exact hNind hxN hyN hne
  let D := G.induce (B : Set (Fin 21))
  have hrem := RamseyDeficiency.removed G ht w
  dsimp only at hrem
  change D.edgeFinset.card + ∑ u ∈ N, G.degree u ≤ G.edgeFinset.card at hrem
  have hsumN_eq : (∑ u ∈ N, (B.filter (G.Adj u)).card) + 3 = ∑ u ∈ N, G.degree u := by
    have hs := Finset.sum_congr (s₁ := N) (s₂ := N) rfl (fun u hu => hdeg_split u hu)
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, hNcard] at hs
    exact hs
  have hD_le40 : D.edgeFinset.card ≤ 40 := by omega
  have hB_small : Small G B 6 := by
    intro S hSB hSind
    by_contra! h6
    have hwS : w ∉ S := fun hwS => ((Gᶜ.mem_neighborFinset w w).mp (hSB hwS)).1 rfl
    apply hi.mono (show 7 ≤ (insert w S).card by rw [Finset.card_insert_of_notMem hwS]; omega) (insert w S)
    refine ⟨?_, rfl⟩
    rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem hwS]
    exact ⟨hSind, fun x hx => (Gᶜ.mem_neighborFinset w x).mp (hSB hx)⟩
  have hB_min3 : ∀ x ∈ B, 3 ≤ (B.filter (G.Adj x)).card := by
    intro x hxB
    by_contra! hlt3
    let R := (B.erase x).filter (fun y => ¬ G.Adj x y)
    have hR_card : 14 ≤ R.card := by
      have h1 : (B.erase x).card = 16 := by rw [Finset.card_erase_of_mem hxB, hBcard]
      have h2 := Finset.card_filter_add_card_filter_not (s := B.erase x) (p := G.Adj x)
      have h3 : ((B.erase x).filter (G.Adj x)).card ≤ (B.filter (G.Adj x)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset x B))
      change ((B.erase x).filter (G.Adj x)).card + R.card = (B.erase x).card at h2
      omega
    obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset (α := Fin 14) (s := R) (by simpa using hR_card)
    let K := G.comap f
    let emb : K ↪g G := SimpleGraph.Embedding.comap f G
    apply h14 K
    refine ⟨SimpleGraph.CliqueFree.comap emb.isContained ht, ?_⟩
    intro S hS
    let S' := S.map f
    have hS'R : ∀ y ∈ S', y ∈ R := fun y hy => by
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hy
      exact hf ⟨i, rfl⟩
    have hx_not : x ∉ S' := fun hxS => (Finset.mem_erase.mp (Finset.mem_filter.mp (hS'R x hxS)).1).1 rfl
    have hS'ind : Gᶜ.IsClique (S' : Set (Fin 21)) := by
      intro a ha b hb hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
      exact (SimpleGraph.Embedding.complEquiv emb).map_adj_iff.mpr
        (hS.isClique hi hj (fun h => hne (congrArg f h)))
    have hins : Gᶜ.IsClique ((insert x S' : Finset (Fin 21)) : Set (Fin 21)) := by
      rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem hx_not]
      refine ⟨hS'ind, fun y hy => ?_⟩
      have hyR := Finset.mem_filter.mp (hS'R y hy)
      exact ⟨(Finset.mem_erase.mp hyR.1).1.symm, hyR.2⟩
    have hsub : insert x S' ⊆ B := Finset.insert_subset hxB (fun y hy =>
      Finset.erase_subset x B (Finset.mem_filter.mp (hS'R y hy)).1)
    have hlt6 := hB_small (insert x S') hsub hins
    rw [Finset.card_insert_of_notMem hx_not, Finset.card_map, hS.card_eq] at hlt6
    omega
  have hB_deg_eq (x : B) : (B.filter (G.Adj x.1)).card = D.degree x := by
    rw [← D.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    refine Finset.card_bij (fun y hy => ⟨y, (Finset.mem_filter.mp hy).1⟩) ?_ ?_ ?_
    · intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
    · intro y₁ _ y₂ _ h
      exact congrArg Subtype.val h
    · intro y hy
      exact ⟨y.1, Finset.mem_filter.mpr ⟨y.2, (Finset.mem_filter.mp hy).2⟩, rfl⟩
  have hB_sum_deg : ∑ x ∈ B, (B.filter (G.Adj x)).card = 2 * D.edgeFinset.card := by
    calc ∑ x ∈ B, (B.filter (G.Adj x)).card
        = ∑ x : B, (B.filter (G.Adj x.1)).card := (Finset.sum_coe_sort B _).symm
      _ = ∑ x : B, D.degree x := Finset.sum_congr rfl (fun x _ => hB_deg_eq x)
      _ = 2 * D.edgeFinset.card := D.sum_degrees_eq_twice_card_edges
  have hB_low : B.Nonempty → ∃ x ∈ B, (B.filter (G.Adj x)).card ≤ 4 := by
    intro _
    by_contra! hall5
    have hsum85 : 85 ≤ ∑ x ∈ B, (B.filter (G.Adj x)).card := by
      calc 85 = ∑ _x ∈ B, (5 : ℕ) := by rw [Finset.sum_const, smul_eq_mul, hBcard]
        _ ≤ ∑ x ∈ B, (B.filter (G.Adj x)).card := Finset.sum_le_sum (fun x hx => hall5 x hx)
    omega
  have hn (l : List (Fin 21)) := relabel_real G (renumber (encode G l)) l
  obtain ⟨vs, d, b, cs, hvs_nd, hvs_cov, hd_le4, hb_mem, hcs_ext, hvs_enc, ⟨r, hrB, hrd⟩⟩ :=
    rootSplitting G ht normalized hn 5 B (Finset.card_pos.mp (by omega)) 4 hB_small hB_low
  have hd_ge3 : 3 ≤ d := hrd ▸ hB_min3 r hrB
  have hvs_edges : edges_ (encode G vs) = D.edgeFinset.card := by
    have dg : degrees (encode G vs) = vs.map (fun x => (B.filter (G.Adj x)).card) := by
      rw [degrees_encode]
      apply List.map_congr_left
      intro x _
      rw [sizeAt_finset G hvs_nd, hvs_cov]
    have hsum_vs := List.sum_toFinset (fun x => (B.filter (G.Adj x)).card) hvs_nd
    rw [hvs_cov, hB_sum_deg] at hsum_vs
    have he := energy (encode G vs)
    rw [dg, ← hsum_vs] at he
    omega
  have h_att_le40 : edges_ (attach cs b) ≤ 40 := by rw [← hvs_enc, hvs_edges]; exact hD_le40
  have hb' : b ∈ levels normalized 5 (16 - d) 4 := by simpa [hBcard] using hb_mem
  interval_cases d
  · -- d = 3: b = b3_0
    have ok := of_decide_eq_true (List.all_eq_true.mp smaller3 b hb')
    simp only [roots3, List.mem_cons, List.not_mem_nil, or_false] at ok
    change b = b3_0 at ok
    subst ok
    have h40 := b3_0_40_ok cs hcs_ext
    have hmem_sol := classify_via_poolOk b3_0 pool_b3_0 sols_b3_0 cs hcs_ext (by omega) pool_b3_0_ok enum_b3_0_ok
    simp [sols_b3_0] at hmem_sol
  · -- d = 4: b ∈ roots4
    have ok := of_decide_eq_true (List.all_eq_true.mp smaller4 b hb')
    simp only [roots4, List.mem_cons, List.not_mem_nil, or_false] at ok
    change b = b4_0 ∨ b = b4_1 ∨ b = b4_2 ∨ b = b4_3 ∨ b = b4_4 ∨ b = b4_5 ∨
      b = b4_6 ∨ b = b4_7 ∨ b = b4_8 ∨ b = b4_9 ∨ b = b4_10 ∨ b = b4_11 at ok
    rcases ok with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · -- b4_0 (4 solutions)
      have h40 := b4_0_40_ok cs hcs_ext
      have hD40 : D.edgeFinset.card = 40 := by rw [← hvs_edges, hvs_enc]; omega
      have hmem_sol := classify_via_poolOk4 b4_0 pool_b4_0 sols_b4_0 cs hcs_ext (by omega) (by decide) pool_b4_0_ok enum_b4_0_ok
      simp only [sols_b4_0, List.mem_cons, List.not_mem_nil, or_false] at hmem_sol
      rcases hmem_sol with rfl | rfl | rfl | rfl
      · exact kill_via_relabel G ht hi N B hNcard hNind hdisjNB (by omega) vs hvs_nd hvs_cov (attach [142, 804, 1553, 2241] b4_0) g17_rep0 hvs_enc sw17_0 rel17_0 9 55 w17_rep0 cert17_rep0
      · exact kill_via_relabel G ht hi N B hNcard hNind hdisjNB (by omega) vs hvs_nd hvs_cov (attach [526, 801, 1169, 2244] b4_0) g17_rep0 hvs_enc sw17_1 rel17_1 9 55 w17_rep0 cert17_rep0
      · exact kill_via_relabel G ht hi N B hNcard hNind hdisjNB (by omega) vs hvs_nd hvs_cov (attach [1121, 1546, 2194, 2340] b4_0) g17_rep0 hvs_enc sw17_2 rel17_2 9 55 w17_rep0 cert17_rep0
      · exact kill_via_relabel G ht hi N B hNcard hNind hdisjNB (by omega) vs hvs_nd hvs_cov (attach [1170, 1576, 2145, 2310] b4_0) g17_rep0 hvs_enc sw17_3 rel17_3 9 55 w17_rep0 cert17_rep0
    · -- b4_1 (8 solutions)
      have h40 := b4_1_40_ok cs hcs_ext
      have hD40 : D.edgeFinset.card = 40 := by rw [← hvs_edges, hvs_enc]; omega
      have hmem_sol := classify_via_poolOk b4_1 pool_b4_1 sols_b4_1 cs hcs_ext (by omega) pool_b4_1_ok enum_b4_1_ok
      simp only [sols_b4_1, List.mem_cons, List.not_mem_nil, or_false] at hmem_sol
      rcases hmem_sol with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact kill_via_relabel G ht hi N B hNcard hNind hdisjNB (by omega) vs hvs_nd hvs_cov (attach [1034, 1569, 2145, 2322] b4_1) g17_rep1 hvs_enc sw17_4 rel17_4 7 41 w17_rep1 cert17_rep1
      · exact kill_via_relabel G ht hi N B hNcard hNind hdisjNB (by omega) vs hvs_nd hvs_cov (attach [1057, 1546, 2194, 2340] b4_1) g17_rep1 hvs_enc sw17_5 rel17_5 7 41 w17_rep1 cert17_rep1
      · exact kill_via_relabel G ht hi N B hNcard hNind hdisjNB (by omega) vs hvs_nd hvs_cov (attach [1154, 1569, 2145, 2310] b4_1) g17_rep0 hvs_enc sw17_6 rel17_6 9 55 w17_rep0 cert17_rep0
      · exact kill_via_relabel G ht hi N B hNcard hNind hdisjNB (by omega) vs hvs_nd hvs_cov (attach [1162, 1569, 2145, 2306] b4_1) g17_rep0 hvs_enc sw17_7 rel17_7 9 55 w17_rep0 cert17_rep0
      · exact kill_via_relabel G ht hi N B hNcard hNind hdisjNB (by omega) vs hvs_nd hvs_cov (attach [1170, 1568, 2145, 2310] b4_1) g17_rep1 hvs_enc sw17_8 rel17_8 7 41 w17_rep1 cert17_rep1
      · exact kill_via_relabel G ht hi N B hNcard hNind hdisjNB (by omega) vs hvs_nd hvs_cov (attach [1546, 1569, 2066, 2148] b4_1) g17_rep0 hvs_enc sw17_9 rel17_9 9 55 w17_rep0 cert17_rep0
      · exact kill_via_relabel G ht hi N B hNcard hNind hdisjNB (by omega) vs hvs_nd hvs_cov (attach [1546, 1569, 2084, 2194] b4_1) g17_rep0 hvs_enc sw17_10 rel17_10 9 55 w17_rep0 cert17_rep0
      · exact kill_via_relabel G ht hi N B hNcard hNind hdisjNB (by omega) vs hvs_nd hvs_cov (attach [1546, 1569, 2144, 2322] b4_1) g17_rep1 hvs_enc sw17_11 rel17_11 7 41 w17_rep1 cert17_rep1
    · have h41 := viaDual41 b4_2 cs 4 4 31 b4_2_41_w hcs_ext b4_2_41_cert; omega
    · have h41 := viaDual41 b4_3 cs 4 3 25 b4_3_41_w hcs_ext b4_3_41_cert; omega
    · have h41 := viaDual41 b4_4 cs 4 1 8 b4_4_41_w hcs_ext b4_4_41_cert; omega
    · have h41 := viaDual41 b4_5 cs 4 8 53 b4_5_41_w hcs_ext b4_5_41_cert; omega
    · -- b4_6 (2 solutions, filtered via S_sol dual cert!)
      have h40 := b4_6_40_ok cs hcs_ext
      have hD40 : D.edgeFinset.card = 40 := by rw [← hvs_edges, hvs_enc]; omega
      have hcs_in_6 : ∀ x ∈ cs, x ∈ pool_b4_6 := by
        by_contra! hnot
        have hcap3 : (cs.map (penalty (fun x => decide (x ∈ pool_b4_6)))).sum ≤ 3 := by
          by_contra! hge4
          have hall := all_of_penalty_ge (fun x => decide (x ∈ pool_b4_6)) cs (by rw [hcs_ext.1]; omega)
          obtain ⟨x, hx, hxn⟩ := hnot
          exact hxn (of_decide_eq_true (hall x hx))
        have h41 := viaDual41Pen b4_6 cs 4 hcs_ext (fun x => decide (x ∈ pool_b4_6)) 3 9 3 72 b4_6_excl_w b4_6_excl_cert hcap3
        omega
      have hmem_sol := classify_via_enum b4_6 pool_b4_6 sols_b4_6 cs hcs_ext (by omega)
        pool_b4_6_sorted.1 hcs_in_6 pool_b4_6_sorted.2 enum_b4_6_ok
      simp only [sols_b4_6, List.mem_cons, List.not_mem_nil, or_false] at hmem_sol
      rcases hmem_sol with rfl | rfl
      · exact kill_via_relabel G ht hi N B hNcard hNind hdisjNB (by omega) vs hvs_nd hvs_cov (attach [262, 1186, 1537, 2369] b4_6) g17_rep1 hvs_enc sw17_12 rel17_12 7 41 w17_rep1 cert17_rep1
      · exact kill_via_relabel G ht hi N B hNcard hNind hdisjNB (by omega) vs hvs_nd hvs_cov (attach [785, 1038, 1057, 2306] b4_6) g17_rep1 hvs_enc sw17_13 rel17_13 7 41 w17_rep1 cert17_rep1
    · have h41 := viaDual41 b4_7 cs 4 0 4 b4_7_41_w hcs_ext b4_7_41_cert; omega
    · have h41 := viaDual41 b4_8 cs 4 1 8 b4_8_41_w hcs_ext b4_8_41_cert; omega
    · have h41 := viaDual41 b4_9 cs 4 1 8 b4_9_41_w hcs_ext b4_9_41_cert; omega
    · have h41 := viaDual41 b4_10 cs 4 0 4 b4_10_41_w hcs_ext b4_10_41_cert; omega
    · have h41 := viaDual41 b4_11 cs 4 2 12 b4_11_41_w hcs_ext b4_11_41_cert; omega

end OMA.RamseyFinite
end RamseyFiniteSection

namespace OMA.Ramsey37Density

open RamseyNumbers SimpleGraph Finset

lemma eighteen_works : IsGraphRamsey 18 3 6 := by
  classical
  rintro G ⟨hG, hc⟩
  have hdeg (v : Fin 18) : G.degree v = 4 ∨ G.degree v = 5 := by
    have hd := degree_lt G hG hc v
    have hdc := nonneighbors_lt fourteen_works G hG hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  by_cases h4 : ∃ v, G.degree v = 4
  · exact OMA.RamseyFinite.no_deg4_18 G hG hc (fun v => by rcases hdeg v with h | h <;> omega) h4
  · push Not at h4
    have hreg : ∀ v, G.degree v = 5 := fun v => by
      rcases hdeg v with h | h
      · exact (h4 v h).elim
      · exact h
    exact OMA.Ramsey36Canonical.regular_impossible G hG hreg hc

end OMA.Ramsey37Density

theorem OMA.solution : OMA.R_RamseyNumbers_ramsey_number_three_nine_R2.H3 := by
  classical
  intro V _ _ D _ hcard ht hi hedges w
  by_contra! hlt
  let e : Fin 21 ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  let G : SimpleGraph (Fin 21) := D.comap e
  let iso : G ≃g D := { toEquiv := e, map_rel_iff' := Iff.rfl }
  have htG : G.CliqueFree 3 := SimpleGraph.CliqueFree.comap iso.toEmbedding.isContained ht
  have hiG : Gᶜ.CliqueFree 7 := SimpleGraph.CliqueFree.comap (SimpleGraph.Embedding.complEquiv iso.toEmbedding).isContained hi
  have hdeg_eq (i : Fin 21) : G.degree i = D.degree (e i) := (iso.degree_eq i).symm
  have hedgesG : G.edgeFinset.card = 52 := by
    have hsumG := G.sum_degrees_eq_twice_card_edges
    have hsumD := D.sum_degrees_eq_twice_card_edges
    have hsum_eq : ∑ i : Fin 21, G.degree i = ∑ x : V, D.degree x := by
      calc ∑ i : Fin 21, G.degree i = ∑ i : Fin 21, D.degree (e i) :=
            Finset.sum_congr rfl (fun i _ => hdeg_eq i)
        _ = ∑ x : V, D.degree x := Equiv.sum_comp e (fun x => D.degree x)
    omega
  let w0 : Fin 21 := e.symm w
  have hw0_lt : G.degree w0 < 4 := by
    rw [hdeg_eq w0, Equiv.apply_symm_apply]
    exact hlt
  have hw0_ge3 : 3 ≤ G.degree w0 := by
    have hdc := OMA.Ramsey37Density.nonneighbors_lt OMA.Ramsey37Density.eighteen_works G htG hiG w0
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  exact OMA.RamseyFinite.no_deg3_21_52 G htG hiG hedgesG w0 (by omega)
    OMA.Ramsey37Density.fourteen_works
    OMA.Ramsey37Density.nine_works
