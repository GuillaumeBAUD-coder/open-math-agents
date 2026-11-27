import OMAReductions.R_RamseyNumbers_ramsey_number_three_six_R1

/-!
# The regular case of the Ramsey number R(3,6)

David Cariolaro, *On the Ramsey number R(3,6)*, Australasian Journal of
Combinatorics 37 (2007), 301–304, gives the structure of the neighborhoods in
a hypothetical counterexample. The twelve vertices outside a closed
neighborhood have different masks on its five neighbors. These masks have
size one or two, and each neighbor occurs four times. A finite calculation
puts the masks in canonical order. Five potential independent sets then force
an edge inside the independent neighborhood of a single vertex.
-/

-- Credit: @MrSeizy
-- The 12-vertex neighborhood argument adapts the H1 proof by @michielkosters.

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
    have hlt := OMA.R_RamseyNumbers_ramsey_number_three_six_R1.degree_lt H hH hHc i
    have hnl := OMA.R_RamseyNumbers_ramsey_number_three_six_R1.nonneighbors_lt
      OMA.R_RamseyNumbers_ramsey_number_three_six_R1.nine_works H hH hHc i
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

theorem OMA.solution : OMA.R_RamseyNumbers_ramsey_number_three_six_R1.H2 := by
  exact OMA.Ramsey36Canonical.regular_impossible
