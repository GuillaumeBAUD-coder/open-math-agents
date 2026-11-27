import FormalConjectures.Wikipedia.SidorenkoConjecture

/-!
Tournament Anti-Sidorenko property for the (2,3,4)-spider tree.
We establish graph isomorphism from any tree satisfying IsSpider234 to the canonical
10-vertex spider on Fin 10, orient it as P_{3,4} union P_2 glued at vertex 4, and prove
the homomorphism density upper bound (1 / 2) ^ 9 via the 32-fold Markov-tree entropy
sandwich decomposition.
-/

open SimpleGraph Finset

namespace Spider234Proof

-- Canonical undirected (2,3,4)-spider adjacency on Fin 10:
-- Leg of length 4: 0 - 1 - 2 - 3 - 4
-- Leg of length 3: 4 - 5 - 6 - 7
-- Leg of length 2: 4 - 8 - 9
def spiderUndirAdj (i j : Fin 10) : Bool :=
  (i == 0 && j == 1) || (i == 1 && j == 0) ||
  (i == 1 && j == 2) || (i == 2 && j == 1) ||
  (i == 2 && j == 3) || (i == 3 && j == 2) ||
  (i == 3 && j == 4) || (i == 4 && j == 3) ||
  (i == 4 && j == 5) || (i == 5 && j == 4) ||
  (i == 5 && j == 6) || (i == 6 && j == 5) ||
  (i == 6 && j == 7) || (i == 7 && j == 6) ||
  (i == 4 && j == 8) || (i == 8 && j == 4) ||
  (i == 8 && j == 9) || (i == 9 && j == 8)

-- Canonical oriented (2,3,4)-spider on Fin 10:
-- Arcs: 0->1, 1->2, 2->3, 4->3, 5->4, 6->5, 7->6, 4->8, 8->9
def spiderDirAdj (i j : Fin 10) : Bool :=
  (i == 0 && j == 1) ||
  (i == 1 && j == 2) ||
  (i == 2 && j == 3) ||
  (i == 4 && j == 3) ||
  (i == 5 && j == 4) ||
  (i == 6 && j == 5) ||
  (i == 7 && j == 6) ||
  (i == 4 && j == 8) ||
  (i == 8 && j == 9)

def D0 : Digraph (Fin 10) where
  Adj i j := spiderDirAdj i j = true

instance : DecidableRel D0.Adj := fun i j => inferInstanceAs (Decidable (spiderDirAdj i j = true))

lemma spiderDir_imp_undir (i j : Fin 10) :
    spiderDirAdj i j = true → spiderUndirAdj i j = true := by
  fin_cases i <;> fin_cases j <;> decide

lemma spiderUndir_iff_dir (i j : Fin 10) :
    spiderUndirAdj i j = true → (spiderDirAdj i j = true ↔ ¬ spiderDirAdj j i = true) := by
  fin_cases i <;> fin_cases j <;> decide

/- ### Section 1: Isomorphism of any IsSpider234 tree with the canonical Fin 10 spider -/

private lemma permute_three_multiset {a b c : ℕ}
    (h : ({a, b, c} : Multiset ℕ) = {2, 3, 4}) :
    (a = 2 ∧ b = 3 ∧ c = 4) ∨ (a = 2 ∧ b = 4 ∧ c = 3) ∨
    (a = 3 ∧ b = 2 ∧ c = 4) ∨ (a = 3 ∧ b = 4 ∧ c = 2) ∨
    (a = 4 ∧ b = 2 ∧ c = 3) ∨ (a = 4 ∧ b = 3 ∧ c = 2) := by
  have hsum : a + b + c = 9 := by
    have := congrArg Multiset.sum h
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at this
    omega
  have hprod : a * b * c = 24 := by
    have := congrArg Multiset.prod h
    simp only [Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton] at this
    linarith
  have ha : a ∈ ({2, 3, 4} : Multiset ℕ) := by rw [← h]; simp
  have hb : b ∈ ({2, 3, 4} : Multiset ℕ) := by rw [← h]; simp
  have hc : c ∈ ({2, 3, 4} : Multiset ℕ) := by rw [← h]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha hb hc
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl
  all_goals try decide
  all_goals norm_num at hprod

private lemma neighborFinset_eq_singleton {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] {v a : V}
    (hdeg : T.degree v = 1) (ha : T.Adj v a) :
    T.neighborFinset v = {a} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx, mem_neighborFinset]
    exact ha
  · rw [card_neighborFinset_eq_degree, hdeg, Finset.card_singleton]

private lemma neighborFinset_eq_pair {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] {v a b : V}
    (hdeg : T.degree v ≤ 2) (hab : a ≠ b) (ha : T.Adj v a) (hb : T.Adj v b) :
    T.neighborFinset v = {a, b} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_neighborFinset]
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · rw [card_neighborFinset_eq_degree, Finset.card_pair hab]
    exact hdeg

private lemma neighborFinset_eq_triple {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] {v a b c : V}
    (hdeg : T.degree v = 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : T.Adj v a) (hb : T.Adj v b) (hc : T.Adj v c) :
    T.neighborFinset v = {a, b, c} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_neighborFinset]
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  · rw [card_neighborFinset_eq_degree, hdeg]
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]

private lemma adj_of_deg_le_two_eq {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] {v a b x : V}
    (hdeg : T.degree v ≤ 2) (hab : a ≠ b) (ha : T.Adj v a) (hb : T.Adj v b)
    (hx : T.Adj v x) (hxa : x ≠ a) : x = b := by
  have hnb := neighborFinset_eq_pair T hdeg hab ha hb
  have hmem : x ∈ T.neighborFinset v := (mem_neighborFinset T v x).mpr hx
  rw [hnb, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · exact absurd rfl hxa
  · rfl

private lemma exists_walk_len_two {V : Type*} (T : SimpleGraph V) {u v : V}
    (hw : ∃ w : T.Walk u v, w.length = 2) :
    ∃ x : V, T.Adj u x ∧ T.Adj x v := by
  obtain ⟨w, hlen⟩ := hw
  cases w with
  | nil => cases hlen
  | @cons _ x _ hux w1 =>
    cases w1 with
    | nil => cases hlen
    | @cons _ y _ hxy w2 =>
      cases w2 with
      | nil => exact ⟨x, hux, hxy⟩
      | cons _ _ => simp [SimpleGraph.Walk.length_cons] at hlen

private lemma exists_walk_len_three {V : Type*} (T : SimpleGraph V) {u v : V}
    (hw : ∃ w : T.Walk u v, w.length = 3) :
    ∃ x y : V, T.Adj u x ∧ T.Adj x y ∧ T.Adj y v := by
  obtain ⟨w, hlen⟩ := hw
  cases w with
  | nil => cases hlen
  | @cons _ x _ hux w1 =>
    obtain ⟨y, hxy, hyv⟩ := exists_walk_len_two T ⟨w1, by simpa using hlen⟩
    exact ⟨x, y, hux, hxy, hyv⟩

private lemma exists_walk_len_four {V : Type*} (T : SimpleGraph V) {u v : V}
    (hw : ∃ w : T.Walk u v, w.length = 4) :
    ∃ x y z : V, T.Adj u x ∧ T.Adj x y ∧ T.Adj y z ∧ T.Adj z v := by
  obtain ⟨w, hlen⟩ := hw
  cases w with
  | nil => cases hlen
  | @cons _ x _ hux w1 =>
    obtain ⟨y, z, hxy, hyz, hzv⟩ := exists_walk_len_three T ⟨w1, by simpa using hlen⟩
    exact ⟨x, y, z, hux, hxy, hyz, hzv⟩

private lemma dist_le_of_adj {V : Type*} (T : SimpleGraph V) {u v : V} (h : T.Adj u v) :
    T.dist u v ≤ 1 :=
  SimpleGraph.dist_le (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)

lemma spider_iso {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (hSpider : SidorenkoConjecture.IsSpider234 T) :
    ∃ e : Fin 10 ≃ V, ∀ i j : Fin 10, T.Adj (e i) (e j) ↔ spiderUndirAdj i j = true := by
  obtain ⟨hTree, hCard, center, l₁, l₂, l₃, hdeg_c, hdeg_le, _, _, _, hd1, hd2, hd3, hmult⟩ :=
    hSpider
  have hleaves : ∃ u2 u3 u4 : V,
      T.degree u2 = 1 ∧ T.degree u3 = 1 ∧ T.degree u4 = 1 ∧
      T.dist center u2 = 2 ∧ T.dist center u3 = 3 ∧ T.dist center u4 = 4 := by
    rcases permute_three_multiset hmult with
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact ⟨l₁, l₂, l₃, hd1, hd2, hd3, h1, h2, h3⟩
    · exact ⟨l₁, l₃, l₂, hd1, hd3, hd2, h1, h3, h2⟩
    · exact ⟨l₂, l₁, l₃, hd2, hd1, hd3, h2, h1, h3⟩
    · exact ⟨l₃, l₁, l₂, hd3, hd1, hd2, h3, h1, h2⟩
    · exact ⟨l₂, l₃, l₁, hd2, hd3, hd1, h2, h3, h1⟩
    · exact ⟨l₃, l₂, l₁, hd3, hd2, hd1, h3, h2, h1⟩
  obtain ⟨u2, u3, u4, hdu2, hdu3, hdu4, hdist2, hdist3, hdist4⟩ := hleaves
  have hconn := hTree.connected
  obtain ⟨c1, hc_c1, hc1_u2⟩ := exists_walk_len_two T
    (by rw [← hdist2]; exact (hconn center u2).exists_walk_length_eq_dist)
  obtain ⟨b1, b2, hc_b1, hb1_b2, hb2_u3⟩ := exists_walk_len_three T
    (by rw [← hdist3]; exact (hconn center u3).exists_walk_length_eq_dist)
  obtain ⟨a3, a2, a1, hc_a3, ha3_a2, ha2_a1, ha1_u4⟩ := exists_walk_len_four T
    (by rw [← hdist4]; exact (hconn center u4).exists_walk_length_eq_dist)
  have hdc_c : T.dist center center = 0 := SimpleGraph.dist_self
  have hdc_a3 : T.dist center a3 = 1 := by
    have hle : T.dist center a3 ≤ 1 := dist_le_of_adj T hc_a3
    have hge : 4 ≤ T.dist center a3 + 3 := by
      calc 4 = T.dist center u4 := hdist4.symm
        _ ≤ T.dist center a3 + T.dist a3 u4 := hconn.dist_triangle
        _ ≤ T.dist center a3 + 3 := Nat.add_le_add_left
          (SimpleGraph.dist_le (SimpleGraph.Walk.cons ha3_a2
            (SimpleGraph.Walk.cons ha2_a1 (SimpleGraph.Walk.cons ha1_u4 .nil)))) _
    omega
  have hdc_a2 : T.dist center a2 = 2 := by
    have hle : T.dist center a2 ≤ 2 :=
      SimpleGraph.dist_le (SimpleGraph.Walk.cons hc_a3 (SimpleGraph.Walk.cons ha3_a2 .nil))
    have hge : 4 ≤ T.dist center a2 + 2 := by
      calc 4 = T.dist center u4 := hdist4.symm
        _ ≤ T.dist center a2 + T.dist a2 u4 := hconn.dist_triangle
        _ ≤ T.dist center a2 + 2 := Nat.add_le_add_left
          (SimpleGraph.dist_le (SimpleGraph.Walk.cons ha2_a1
            (SimpleGraph.Walk.cons ha1_u4 .nil))) _
    omega
  have hdc_a1 : T.dist center a1 = 3 := by
    have hle : T.dist center a1 ≤ 3 :=
      SimpleGraph.dist_le (SimpleGraph.Walk.cons hc_a3
        (SimpleGraph.Walk.cons ha3_a2 (SimpleGraph.Walk.cons ha2_a1 .nil)))
    have hge : 4 ≤ T.dist center a1 + 1 := by
      calc 4 = T.dist center u4 := hdist4.symm
        _ ≤ T.dist center a1 + T.dist a1 u4 := hconn.dist_triangle
        _ ≤ T.dist center a1 + 1 := Nat.add_le_add_left (dist_le_of_adj T ha1_u4) _
    omega
  have hdc_b1 : T.dist center b1 = 1 := by
    have hle : T.dist center b1 ≤ 1 := dist_le_of_adj T hc_b1
    have hge : 3 ≤ T.dist center b1 + 2 := by
      calc 3 = T.dist center u3 := hdist3.symm
        _ ≤ T.dist center b1 + T.dist b1 u3 := hconn.dist_triangle
        _ ≤ T.dist center b1 + 2 := Nat.add_le_add_left
          (SimpleGraph.dist_le (SimpleGraph.Walk.cons hb1_b2
            (SimpleGraph.Walk.cons hb2_u3 .nil))) _
    omega
  have hdc_b2 : T.dist center b2 = 2 := by
    have hle : T.dist center b2 ≤ 2 :=
      SimpleGraph.dist_le (SimpleGraph.Walk.cons hc_b1 (SimpleGraph.Walk.cons hb1_b2 .nil))
    have hge : 3 ≤ T.dist center b2 + 1 := by
      calc 3 = T.dist center u3 := hdist3.symm
        _ ≤ T.dist center b2 + T.dist b2 u3 := hconn.dist_triangle
        _ ≤ T.dist center b2 + 1 := Nat.add_le_add_left (dist_le_of_adj T hb2_u3) _
    omega
  have hdc_c1 : T.dist center c1 = 1 := by
    have hle : T.dist center c1 ≤ 1 := dist_le_of_adj T hc_c1
    have hge : 2 ≤ T.dist center c1 + 1 := by
      calc 2 = T.dist center u2 := hdist2.symm
        _ ≤ T.dist center c1 + T.dist c1 u2 := hconn.dist_triangle
        _ ≤ T.dist center c1 + 1 := Nat.add_le_add_left (dist_le_of_adj T hc1_u2) _
    omega
  have hdeg_a1_ge : 2 ≤ T.degree a1 := by
    have hne : a2 ≠ u4 := fun h => by rw [h] at hdc_a2; omega
    have hsub : ({a2, u4} : Finset V) ⊆ T.neighborFinset a1 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [mem_neighborFinset]
      rcases hx with rfl | rfl
      · exact ha2_a1.symm
      · exact ha1_u4
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hne, card_neighborFinset_eq_degree] at this
  have hdeg_a2_ge : 2 ≤ T.degree a2 := by
    have hne : a3 ≠ a1 := fun h => by rw [h] at hdc_a3; omega
    have hsub : ({a3, a1} : Finset V) ⊆ T.neighborFinset a2 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [mem_neighborFinset]
      rcases hx with rfl | rfl
      · exact ha3_a2.symm
      · exact ha2_a1
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hne, card_neighborFinset_eq_degree] at this
  have hdeg_b2_ge : 2 ≤ T.degree b2 := by
    have hne : b1 ≠ u3 := fun h => by rw [h] at hdc_b1; omega
    have hsub : ({b1, u3} : Finset V) ⊆ T.neighborFinset b2 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [mem_neighborFinset]
      rcases hx with rfl | rfl
      · exact hb1_b2.symm
      · exact hb2_u3
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hne, card_neighborFinset_eq_degree] at this
  have ha3_ne_c : a3 ≠ center := fun h => by rw [h] at hdc_a3; omega
  have ha2_ne_c : a2 ≠ center := fun h => by rw [h] at hdc_a2; omega
  have ha1_ne_c : a1 ≠ center := fun h => by rw [h] at hdc_a1; omega
  have hb1_ne_c : b1 ≠ center := fun h => by rw [h] at hdc_b1; omega
  have hb2_ne_c : b2 ≠ center := fun h => by rw [h] at hdc_b2; omega
  have hc1_ne_c : c1 ≠ center := fun h => by rw [h] at hdc_c1; omega
  have hnb_a3 : T.neighborFinset a3 = {center, a2} :=
    neighborFinset_eq_pair T (hdeg_le a3 ha3_ne_c) (Ne.symm ha2_ne_c) hc_a3.symm ha3_a2
  have hnb_a2 : T.neighborFinset a2 = {a3, a1} :=
    neighborFinset_eq_pair T (hdeg_le a2 ha2_ne_c)
      (fun h => by rw [h] at hdc_a3; omega) ha3_a2.symm ha2_a1
  have hnb_a1 : T.neighborFinset a1 = {a2, u4} :=
    neighborFinset_eq_pair T (hdeg_le a1 ha1_ne_c)
      (fun h => by rw [h] at hdc_a2; omega) ha2_a1.symm ha1_u4
  have hnb_u4 : T.neighborFinset u4 = {a1} :=
    neighborFinset_eq_singleton T hdu4 ha1_u4.symm
  have hnb_b1 : T.neighborFinset b1 = {center, b2} :=
    neighborFinset_eq_pair T (hdeg_le b1 hb1_ne_c) (Ne.symm hb2_ne_c) hc_b1.symm hb1_b2
  have hnb_b2 : T.neighborFinset b2 = {b1, u3} :=
    neighborFinset_eq_pair T (hdeg_le b2 hb2_ne_c)
      (fun h => by rw [h] at hdc_b1; omega) hb1_b2.symm hb2_u3
  have hnb_u3 : T.neighborFinset u3 = {b2} :=
    neighborFinset_eq_singleton T hdu3 hb2_u3.symm
  have hnb_c1 : T.neighborFinset c1 = {center, u2} :=
    neighborFinset_eq_pair T (hdeg_le c1 hc1_ne_c)
      (fun h => by rw [← h] at hdist2; omega) hc_c1.symm hc1_u2
  have hnb_u2 : T.neighborFinset u2 = {c1} :=
    neighborFinset_eq_singleton T hdu2 hc1_u2.symm
  have ha3_ne_b1 : a3 ≠ b1 := by
    intro h
    have hb2_eq_a2 : b2 = a2 := by
      apply adj_of_deg_le_two_eq T (hdeg_le a3 ha3_ne_c) (Ne.symm ha2_ne_c) hc_a3.symm ha3_a2
      · rw [h]; exact hb1_b2
      · exact hb2_ne_c
    have hu3_eq_a1 : u3 = a1 := by
      apply adj_of_deg_le_two_eq T (hdeg_le a2 ha2_ne_c)
        (fun hh => by rw [hh] at hdc_a3; omega) ha3_a2.symm ha2_a1
      · rw [← hb2_eq_a2]; exact hb2_u3
      · intro hh; rw [hh] at hdist3; omega
    rw [hu3_eq_a1] at hdu3
    omega
  have ha3_ne_c1 : a3 ≠ c1 := by
    intro h
    have hu2_eq_a2 : u2 = a2 := by
      apply adj_of_deg_le_two_eq T (hdeg_le a3 ha3_ne_c) (Ne.symm ha2_ne_c) hc_a3.symm ha3_a2
      · rw [h]; exact hc1_u2
      · intro hh; rw [hh] at hdist2; omega
    rw [hu2_eq_a2] at hdu2
    omega
  have hb1_ne_c1 : b1 ≠ c1 := by
    intro h
    have hu2_eq_b2 : u2 = b2 := by
      apply adj_of_deg_le_two_eq T (hdeg_le b1 hb1_ne_c) (Ne.symm hb2_ne_c) hc_b1.symm hb1_b2
      · rw [h]; exact hc1_u2
      · intro hh; rw [hh] at hdist2; omega
    rw [hu2_eq_b2] at hdu2
    omega
  have hnb_c : T.neighborFinset center = {a3, b1, c1} :=
    neighborFinset_eq_triple T hdeg_c ha3_ne_b1 ha3_ne_c1 hb1_ne_c1 hc_a3 hc_b1 hc_c1
  have ha2_ne_b2 : a2 ≠ b2 := by
    intro h
    have : a3 ∈ T.neighborFinset b2 := by
      rw [← h, hnb_a2]; simp
    rw [hnb_b2, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl
    · exact ha3_ne_b1 rfl
    · omega
  have ha2_ne_u2 : a2 ≠ u2 := fun h => by rw [h] at hdeg_a2_ge; omega
  have hb2_ne_u2 : b2 ≠ u2 := fun h => by rw [h] at hdeg_b2_ge; omega
  have ha1_ne_u3 : a1 ≠ u3 := fun h => by rw [h] at hdeg_a1_ge; omega
  let f : Fin 10 → V := fun i =>
    if i.val = 0 then u4
    else if i.val = 1 then a1
    else if i.val = 2 then a2
    else if i.val = 3 then a3
    else if i.val = 4 then center
    else if i.val = 5 then b1
    else if i.val = 6 then b2
    else if i.val = 7 then u3
    else if i.val = 8 then c1
    else u2
  let dVec : Fin 10 → ℕ := fun i =>
    if i.val = 0 then 4
    else if i.val = 1 then 3
    else if i.val = 2 then 2
    else if i.val = 3 then 1
    else if i.val = 4 then 0
    else if i.val = 5 then 1
    else if i.val = 6 then 2
    else if i.val = 7 then 3
    else if i.val = 8 then 1
    else 2
  have hf_dist : ∀ i : Fin 10, T.dist center (f i) = dVec i := by
    intro i
    fin_cases i <;> dsimp [f, dVec] <;> assumption
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hd : dVec i = dVec j := by rw [← hf_dist i, ← hf_dist j, hij]
    fin_cases i <;> fin_cases j <;> dsimp [f, dVec] at hij hd
    all_goals try rfl
    all_goals try omega
    · exact absurd hij ha1_ne_u3
    · exact absurd hij ha2_ne_b2
    · exact absurd hij ha2_ne_u2
    · exact absurd hij ha3_ne_b1
    · exact absurd hij ha3_ne_c1
    · exact absurd hij.symm ha3_ne_b1
    · exact absurd hij hb1_ne_c1
    · exact absurd hij.symm ha2_ne_b2
    · exact absurd hij hb2_ne_u2
    · exact absurd hij.symm ha1_ne_u3
    · exact absurd hij.symm ha3_ne_c1
    · exact absurd hij.symm hb1_ne_c1
    · exact absurd hij.symm ha2_ne_u2
    · exact absurd hij.symm hb2_ne_u2
  have hf_bij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hf_inj, by rw [Fintype.card_fin, hCard]⟩
  let e : Fin 10 ≃ V := Equiv.ofBijective f hf_bij
  refine ⟨e, fun i j => ?_⟩
  change T.Adj (f i) (f j) ↔ spiderUndirAdj i j = true
  rw [← mem_neighborFinset]
  have hmem_iff : ∀ a x : Fin 10, f x ∈ ({f a} : Finset V) ↔ x = a := fun a x => by
    simp [hf_inj.eq_iff]
  have hmem_pair : ∀ a b x : Fin 10, f x ∈ ({f a, f b} : Finset V) ↔ (x = a ∨ x = b) :=
    fun a b x => by simp [hf_inj.eq_iff]
  have hmem_triple : ∀ a b c x : Fin 10,
      f x ∈ ({f a, f b, f c} : Finset V) ↔ (x = a ∨ x = b ∨ x = c) :=
    fun a b c x => by simp [hf_inj.eq_iff]
  fin_cases i
  · change f j ∈ T.neighborFinset u4 ↔ _; rw [hnb_u4]; exact (hmem_iff 1 j).trans (by fin_cases j <;> decide)
  · change f j ∈ T.neighborFinset a1 ↔ _; rw [hnb_a1]; exact (hmem_pair 2 0 j).trans (by fin_cases j <;> decide)
  · change f j ∈ T.neighborFinset a2 ↔ _; rw [hnb_a2]; exact (hmem_pair 3 1 j).trans (by fin_cases j <;> decide)
  · change f j ∈ T.neighborFinset a3 ↔ _; rw [hnb_a3]; exact (hmem_pair 4 2 j).trans (by fin_cases j <;> decide)
  · change f j ∈ T.neighborFinset center ↔ _; rw [hnb_c]; exact (hmem_triple 3 5 8 j).trans (by fin_cases j <;> decide)
  · change f j ∈ T.neighborFinset b1 ↔ _; rw [hnb_b1]; exact (hmem_pair 4 6 j).trans (by fin_cases j <;> decide)
  · change f j ∈ T.neighborFinset b2 ↔ _; rw [hnb_b2]; exact (hmem_pair 5 7 j).trans (by fin_cases j <;> decide)
  · change f j ∈ T.neighborFinset u3 ↔ _; rw [hnb_u3]; exact (hmem_iff 6 j).trans (by fin_cases j <;> decide)
  · change f j ∈ T.neighborFinset c1 ↔ _; rw [hnb_c1]; exact (hmem_pair 4 9 j).trans (by fin_cases j <;> decide)
  · change f j ∈ T.neighborFinset u2 ↔ _; rw [hnb_u2]; exact (hmem_iff 8 j).trans (by fin_cases j <;> decide)

/- ### Section 2: Small tournament subgraph counting bounds -/

lemma tournament_asym {W : Type*} (G : Digraph W) {u v : W}
    (hG : G.IsTournament) (h : G.Adj u v) : ¬ G.Adj v u := by
  intro hvu
  by_cases huv : u = v
  · rw [huv] at h; exact hG.1 v h
  · exact ((hG.2 u v huv).mp h) hvu

section SmallBounds

variable {W : Type*} [Fintype W] [DecidableEq W] (G : Digraph W) [DecidableRel G.Adj]

def arcsFinset : Finset (W × W) :=
  Finset.univ.filter (fun p => G.Adj p.1 p.2)

def p2Finset : Finset (W × W × W) :=
  Finset.univ.filter (fun t => G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2)

def p11InFinset : Finset (W × W × W) :=
  Finset.univ.filter (fun t => G.Adj t.2.1 t.1 ∧ G.Adj t.2.2 t.1)

def p12Finset : Finset ((W × W) × (W × W)) :=
  Finset.univ.filter (fun q => G.Adj q.1.1 q.1.2 ∧ G.Adj q.2.1 q.1.2 ∧ G.Adj q.2.2 q.2.1)

def p12RevFinset : Finset ((W × W) × (W × W)) :=
  Finset.univ.filter (fun q => G.Adj q.1.2 q.1.1 ∧ G.Adj q.1.2 q.2.1 ∧ G.Adj q.2.1 q.2.2)

def p22RevFinset : Finset (W × (W × W) × (W × W)) :=
  Finset.univ.filter (fun x =>
    G.Adj x.1 x.2.1.1 ∧ G.Adj x.2.1.1 x.2.1.2 ∧ G.Adj x.1 x.2.2.1 ∧ G.Adj x.2.2.1 x.2.2.2)

lemma two_mul_card_arcs_le (hG : G.IsTournament) :
    2 * (arcsFinset G).card ≤ (Fintype.card W) ^ 2 := by
  let S := arcsFinset G
  let S' := S.image Prod.swap
  have hinj : Function.Injective (Prod.swap : W × W → W × W) := Prod.swap_injective
  have hdisj : Disjoint S S' := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [Finset.mem_image] at hp'
    obtain ⟨q, hq, rfl⟩ := hp'
    simp only [S, arcsFinset, Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap] at hp hq
    exact tournament_asym G hG hq hp
  have hunion : (S ∪ S').card ≤ (Finset.univ : Finset (W × W)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective S hinj,
    Finset.card_univ, Fintype.card_prod] at hunion
  have hsq : Fintype.card W * Fintype.card W = (Fintype.card W) ^ 2 := (sq _).symm
  linarith

private lemma four_mul_le_add_sq (x y : ℕ) : 4 * (x * y) ≤ (x + y) ^ 2 := by
  by_cases h : x ≤ y
  · have h1 : (x + y) ^ 2 = 4 * (x * y) + (y - x) ^ 2 := by zify [h]; ring
    omega
  · have hyx : y ≤ x := le_of_not_ge h
    have h1 : (x + y) ^ 2 = 4 * (x * y) + (x - y) ^ 2 := by zify [hyx]; ring
    omega

lemma four_mul_card_p2_le (hG : G.IsTournament) :
    4 * (p2Finset G).card ≤ (Fintype.card W) ^ 3 := by
  let inN (b : W) := Finset.univ.filter (fun a : W => G.Adj a b)
  let outN (b : W) := Finset.univ.filter (fun c : W => G.Adj b c)
  have hsum : (p2Finset G).card = ∑ b : W, (inN b).card * (outN b).card := by
    have heq : p2Finset G = Finset.univ.biUnion (fun b : W =>
        (inN b ×ˢ outN b).image (fun p : W × W => (p.1, b, p.2))) := by
      ext ⟨a, b, c⟩
      simp only [p2Finset, inN, outN, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Finset.mem_image, Finset.mem_product, Prod.mk.injEq]
      constructor
      · rintro ⟨hab, hbc⟩; exact ⟨b, ⟨a, c⟩, ⟨hab, hbc⟩, rfl, rfl, rfl⟩
      · rintro ⟨b', ⟨a', c'⟩, ⟨ha', hc'⟩, rfl, rfl, rfl⟩; exact ⟨ha', hc'⟩
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset W)) (fun b : W =>
        (inN b ×ˢ outN b).image (fun p : W × W => (p.1, b, p.2))) := by
      intro b1 _ b2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro t ht1 ht2
      rw [Finset.mem_image] at ht1 ht2
      obtain ⟨p1, _, hp1⟩ := ht1
      obtain ⟨p2, _, hp2⟩ := ht2
      rw [← hp1] at hp2
      exact hne (Prod.mk.inj (Prod.mk.inj hp2).2).1.symm
    rw [heq, Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hinj : Function.Injective (fun p : W × W => (p.1, b, p.2)) := by
      intro x y hxy
      exact Prod.ext (Prod.mk.inj hxy).1 (Prod.mk.inj (Prod.mk.inj hxy).2).2
    rw [Finset.card_image_of_injective _ hinj, Finset.card_product]
  have hbound : ∀ b : W, 4 * ((inN b).card * (outN b).card) ≤ (Fintype.card W) ^ 2 := by
    intro b
    have hdisj : Disjoint (inN b) (outN b) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [inN, outN, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
      exact tournament_asym G hG hx1 hx2
    have hle : (inN b).card + (outN b).card ≤ Fintype.card W := by
      rw [← Finset.card_union_of_disjoint hdisj, ← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    exact le_trans (four_mul_le_add_sq _ _) (Nat.pow_le_pow_left hle 2)
  rw [hsum, Finset.mul_sum]
  calc ∑ b : W, 4 * ((inN b).card * (outN b).card)
      ≤ ∑ _b : W, (Fintype.card W) ^ 2 := Finset.sum_le_sum fun b _ => hbound b
    _ = Fintype.card W * (Fintype.card W) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ = (Fintype.card W) ^ 3 := by ring

lemma sixteen_mul_p2_mul_p11In_le (hG : G.IsTournament) :
    16 * ((p2Finset G).card * (p11InFinset G).card) ≤ (Fintype.card W) ^ 6 := by
  let U : Finset ((W × W) × W) := arcsFinset G ×ˢ Finset.univ
  let f1 : W × W × W → (W × W) × W := fun t => ((t.1, t.2.1), t.2.2)
  let f2 : W × W × W → (W × W) × W := fun t => ((t.2.1, t.1), t.2.2)
  have hf1_inj : Function.Injective f1 := fun ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ h => by
    simp only [f1, Prod.mk.injEq] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; rfl
  have hf2_inj : Function.Injective f2 := fun ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ h => by
    simp only [f2, Prod.mk.injEq] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; rfl
  let S1 := (p2Finset G).image f1
  let S2 := (p11InFinset G).image f2
  have hsub : S1 ∪ S2 ⊆ U := by
    intro x hx
    simp only [S1, S2, U, Finset.mem_union, Finset.mem_image, p2Finset, p11InFinset,
      arcsFinset, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hx ⊢
    rcases hx with ⟨⟨a, b, c⟩, ⟨hab, _⟩, rfl⟩ | ⟨⟨a, b, c⟩, ⟨hba, _⟩, rfl⟩
    · exact hab
    · exact hba
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [S1, S2, Finset.mem_image, p2Finset, p11InFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx1 hx2
    obtain ⟨⟨a1, b1, c1⟩, ⟨_, hbc1⟩, heq1⟩ := hx1
    obtain ⟨⟨a2, b2, c2⟩, ⟨_, hca2⟩, heq2⟩ := hx2
    rw [← heq1] at heq2
    simp only [f1, f2, Prod.mk.injEq] at heq2
    obtain ⟨⟨_, rfl⟩, rfl⟩ := heq2
    exact tournament_asym G hG hbc1 hca2
  have hsum_le : (p2Finset G).card + (p11InFinset G).card ≤ (arcsFinset G).card * Fintype.card W := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hf1_inj,
      Finset.card_image_of_injective _ hf2_inj, Finset.card_product, Finset.card_univ] at this
  have h2sum : 2 * ((p2Finset G).card + (p11InFinset G).card) ≤ (Fintype.card W) ^ 3 := by
    calc 2 * ((p2Finset G).card + (p11InFinset G).card)
        ≤ 2 * ((arcsFinset G).card * Fintype.card W) := Nat.mul_le_mul_left 2 hsum_le
      _ = (2 * (arcsFinset G).card) * Fintype.card W := by ring
      _ ≤ (Fintype.card W) ^ 2 * Fintype.card W :=
          Nat.mul_le_mul_right _ (two_mul_card_arcs_le G hG)
      _ = (Fintype.card W) ^ 3 := by ring
  calc 16 * ((p2Finset G).card * (p11InFinset G).card)
      = 4 * (4 * ((p2Finset G).card * (p11InFinset G).card)) := by ring
    _ ≤ 4 * ((p2Finset G).card + (p11InFinset G).card) ^ 2 :=
        Nat.mul_le_mul_left 4 (four_mul_le_add_sq _ _)
    _ = (2 * ((p2Finset G).card + (p11InFinset G).card)) ^ 2 := by ring
    _ ≤ ((Fintype.card W) ^ 3) ^ 2 := Nat.pow_le_pow_left h2sum 2
    _ = (Fintype.card W) ^ 6 := by ring

lemma eight_mul_card_p12_le (hG : G.IsTournament) :
    8 * (p12Finset G).card ≤ (Fintype.card W) ^ 4 := by
  let U : Finset ((W × W) × (W × W)) :=
    Finset.univ.filter (fun q => G.Adj q.1.1 q.1.2 ∧ G.Adj q.2.2 q.2.1)
  let sw : (W × W) × (W × W) → (W × W) × (W × W) := fun q => ((q.2.2, q.2.1), (q.1.2, q.1.1))
  have hsw_inj : Function.Injective sw := fun ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩ ⟨⟨a2, b2⟩, ⟨c2, d2⟩⟩ h => by
    simp only [sw, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := h; rfl
  let S := p12Finset G
  let S' := S.image sw
  have hsub : S ∪ S' ⊆ U := by
    intro q hq
    simp only [S, S', U, p12Finset, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and] at hq ⊢
    rcases hq with ⟨h1, _, h3⟩ | ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨h1, _, h3⟩, rfl⟩
    · exact ⟨h1, h3⟩
    · exact ⟨h3, h1⟩
  have hdisj : Disjoint S S' := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    simp only [S, S', p12Finset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hq1 hq2
    obtain ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨_, hcb, _⟩, rfl⟩ := hq2
    exact tournament_asym G hG hcb hq1.2.1
  have hU_card : U.card = (arcsFinset G).card ^ 2 := by
    let g : (W × W) × (W × W) → (W × W) × (W × W) := fun p => (p.1, (p.2.2, p.2.1))
    have hg_inj : Function.Injective g := fun ⟨p1, c1, d1⟩ ⟨p2, c2, d2⟩ h => by
      simp only [g, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; rfl
    have hU_eq : U = (arcsFinset G ×ˢ arcsFinset G).image g := by
      ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
      simp only [U, arcsFinset, g, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image, Finset.mem_product, Prod.mk.injEq]
      constructor
      · rintro ⟨hab, hdc⟩; exact ⟨⟨(a, b), (d, c)⟩, ⟨hab, hdc⟩, rfl, rfl, rfl⟩
      · rintro ⟨⟨⟨a', b'⟩, ⟨d', c'⟩⟩, ⟨hab, hdc⟩, ⟨rfl, rfl⟩, rfl, rfl⟩; exact ⟨hab, hdc⟩
    rw [hU_eq, Finset.card_image_of_injective _ hg_inj, Finset.card_product, sq]
  have h2le : 2 * S.card ≤ (arcsFinset G).card ^ 2 := by
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hsw_inj, hU_card]
      at this
    omega
  calc 8 * S.card = 4 * (2 * S.card) := by ring
    _ ≤ 4 * (arcsFinset G).card ^ 2 := Nat.mul_le_mul_left 4 h2le
    _ = (2 * (arcsFinset G).card) ^ 2 := by ring
    _ ≤ ((Fintype.card W) ^ 2) ^ 2 := Nat.pow_le_pow_left (two_mul_card_arcs_le G hG) 2
    _ = (Fintype.card W) ^ 4 := by ring

lemma eight_mul_card_p12Rev_le (hG : G.IsTournament) :
    8 * (p12RevFinset G).card ≤ (Fintype.card W) ^ 4 := by
  let U : Finset ((W × W) × (W × W)) :=
    Finset.univ.filter (fun q => G.Adj q.1.2 q.1.1 ∧ G.Adj q.2.1 q.2.2)
  let sw : (W × W) × (W × W) → (W × W) × (W × W) := fun q => ((q.2.2, q.2.1), (q.1.2, q.1.1))
  have hsw_inj : Function.Injective sw := fun ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩ ⟨⟨a2, b2⟩, ⟨c2, d2⟩⟩ h => by
    simp only [sw, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := h; rfl
  let S := p12RevFinset G
  let S' := S.image sw
  have hsub : S ∪ S' ⊆ U := by
    intro q hq
    simp only [S, S', U, p12RevFinset, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and] at hq ⊢
    rcases hq with ⟨h1, _, h3⟩ | ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨h1, _, h3⟩, rfl⟩
    · exact ⟨h1, h3⟩
    · exact ⟨h3, h1⟩
  have hdisj : Disjoint S S' := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    simp only [S, S', p12RevFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hq1 hq2
    obtain ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨_, hbc, _⟩, rfl⟩ := hq2
    exact tournament_asym G hG hbc hq1.2.1
  have hU_card : U.card = (arcsFinset G).card ^ 2 := by
    let g : (W × W) × (W × W) → (W × W) × (W × W) := fun p => ((p.1.2, p.1.1), p.2)
    have hg_inj : Function.Injective g := fun ⟨⟨b1, a1⟩, p2⟩ ⟨⟨b2, a2⟩, q2⟩ h => by
      simp only [g, Prod.mk.injEq] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; rfl
    have hU_eq : U = (arcsFinset G ×ˢ arcsFinset G).image g := by
      ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
      simp only [U, arcsFinset, g, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image, Finset.mem_product, Prod.mk.injEq]
      constructor
      · rintro ⟨hba, hcd⟩; exact ⟨⟨(b, a), (c, d)⟩, ⟨hba, hcd⟩, ⟨rfl, rfl⟩, rfl⟩
      · rintro ⟨⟨⟨b', a'⟩, ⟨c', d'⟩⟩, ⟨hba, hcd⟩, ⟨rfl, rfl⟩, rfl, rfl⟩; exact ⟨hba, hcd⟩
    rw [hU_eq, Finset.card_image_of_injective _ hg_inj, Finset.card_product, sq]
  have h2le : 2 * S.card ≤ (arcsFinset G).card ^ 2 := by
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hsw_inj, hU_card]
      at this
    omega
  calc 8 * S.card = 4 * (2 * S.card) := by ring
    _ ≤ 4 * (arcsFinset G).card ^ 2 := Nat.mul_le_mul_left 4 h2le
    _ = (2 * (arcsFinset G).card) ^ 2 := by ring
    _ ≤ ((Fintype.card W) ^ 2) ^ 2 := Nat.pow_le_pow_left (two_mul_card_arcs_le G hG) 2
    _ = (Fintype.card W) ^ 4 := by ring

lemma sixteen_mul_card_p22Rev_le (hG : G.IsTournament) :
    (16 : ℝ) * ((p22RevFinset G).card : ℝ) ≤ (Fintype.card W : ℝ) ^ 5 := by
  set n : ℝ := (Fintype.card W : ℝ) with hn_def
  let A : W → W → ℝ := fun i j => if G.Adj i j then 1 else if i = j then 1 / 2 else 0
  let U : W → W → ℝ := fun i j => A i j - 1 / 2
  have hU_skew : ∀ i j : W, U j i = - U i j := by
    intro i j
    dsimp [U, A]
    by_cases hij : i = j
    · subst hij
      have h1 : ¬ G.Adj i i := hG.1 i
      simp [h1]
    · have hji : j ≠ i := Ne.symm hij
      have htr := hG.2 i j hij
      by_cases hadj : G.Adj i j
      · have hnot : ¬ G.Adj j i := htr.mp hadj
        simp [hadj, hnot, hji]; ring
      · have hyes : G.Adj j i := Decidable.byContradiction fun hn => hadj (htr.mpr hn)
        simp [hadj, hyes, hij]; ring
  have hU_sq : ∀ i j : W, U i j ^ 2 ≤ 1 / 4 := by
    intro i j
    dsimp [U, A]
    split_ifs <;> norm_num
  let walk2 : W → Finset (W × W) := fun u =>
    Finset.univ.filter (fun p : W × W => G.Adj u p.1 ∧ G.Adj p.1 p.2)
  have hcard_eq : (p22RevFinset G).card = ∑ u : W, (walk2 u).card ^ 2 := by
    have heq : p22RevFinset G = Finset.univ.biUnion (fun u : W =>
        (walk2 u ×ˢ walk2 u).image (fun q => (u, q.1, q.2))) := by
      ext ⟨u, p1, p2⟩
      simp only [p22RevFinset, walk2, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Finset.mem_image, Finset.mem_product, Prod.mk.injEq]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨u, ⟨p1, p2⟩, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, rfl, rfl, rfl⟩
      · rintro ⟨u', ⟨q1, q2⟩, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, rfl, rfl, rfl⟩; exact ⟨h1, h2, h3, h4⟩
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset W)) (fun u : W =>
        (walk2 u ×ˢ walk2 u).image (fun q => (u, q.1, q.2))) := by
      intro u1 _ u2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_image] at hx1 hx2
      obtain ⟨_, _, rfl⟩ := hx1
      obtain ⟨_, _, heq2⟩ := hx2
      exact hne (Prod.mk.inj heq2).1.symm
    rw [heq, Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hinj : Function.Injective (fun q : (W × W) × (W × W) => (u, q.1, q.2)) := by
      intro x y hxy
      exact Prod.ext (Prod.mk.inj (Prod.mk.inj hxy).2).1 (Prod.mk.inj (Prod.mk.inj hxy).2).2
    rw [Finset.card_image_of_injective _ hinj, Finset.card_product, sq]
  let Wf : W → ℝ := fun i => ∑ j : W, A i j * (∑ k : W, A j k)
  have hwalk_le_Wf : ∀ u : W, ((walk2 u).card : ℝ) ≤ Wf u := by
    intro u
    have h1 : ((walk2 u).card : ℝ) =
        ∑ j : W, ∑ k : W, (if G.Adj u j then (1 : ℝ) else 0) * (if G.Adj j k then 1 else 0) := by
      have hcard_nat : (walk2 u).card =
          ∑ p : W × W, if G.Adj u p.1 ∧ G.Adj p.1 p.2 then 1 else 0 := by
        dsimp [walk2]
        rw [Finset.card_filter]
      rw [hcard_nat, Nat.cast_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      by_cases h1 : G.Adj u j <;> by_cases h2 : G.Adj j k <;> simp [h1, h2]
    rw [h1]
    dsimp [Wf]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.mul_sum]
    have hA1 : (if G.Adj u j then (1 : ℝ) else 0) ≤ A u j := by dsimp [A]; split_ifs <;> norm_num
    have hA2 : ∀ k : W, (if G.Adj j k then (1 : ℝ) else 0) ≤ A j k := fun k => by
      dsimp [A]; split_ifs <;> norm_num
    exact mul_le_mul hA1 (Finset.sum_le_sum fun k _ => hA2 k)
      (Finset.sum_nonneg fun k _ => by split_ifs <;> norm_num)
      (by dsimp [A]; split_ifs <;> norm_num)
  have hcard_le_Wf_sq : ((p22RevFinset G).card : ℝ) ≤ ∑ i : W, Wf i ^ 2 := by
    rw [hcard_eq, Nat.cast_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hwalk_le_Wf u) 2
  let v : W → ℝ := fun j => ∑ k : W, U j k
  let y : W → ℝ := fun i => ∑ j : W, U i j * v j
  have hsum_v : ∑ j : W, v j = 0 := by
    have hswap : ∑ j : W, v j = - (∑ j : W, v j) := by
      calc ∑ j : W, ∑ k : W, U j k
          = ∑ k : W, ∑ j : W, U j k := Finset.sum_comm
        _ = ∑ k : W, ∑ j : W, (- U k j) :=
            Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => hU_skew k j
        _ = - ∑ k : W, ∑ j : W, U k j := by simp [Finset.sum_neg_distrib]
    linarith
  have hWf_eq : ∀ i : W, Wf i = n ^ 2 / 4 + (n / 2) * v i + y i := by
    intro i
    have hAj : ∀ j : W, ∑ k : W, A j k = n / 2 + v j := fun j => by
      have : ∀ k : W, A j k = 1 / 2 + U j k := fun k => by dsimp [U]; ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp [v]; rw [← hn_def]; ring
    have hAi : ∀ j : W, A i j = 1 / 2 + U i j := fun j => by dsimp [U]; ring
    dsimp [Wf]
    calc ∑ j : W, A i j * (∑ k : W, A j k)
        = ∑ j : W, (1 / 2 + U i j) * (n / 2 + v j) :=
          Finset.sum_congr rfl fun j _ => by rw [hAi j, hAj j]
      _ = ∑ j : W, (n / 4 + (1 / 2) * v j + (n / 2) * U i j + U i j * v j) :=
          Finset.sum_congr rfl fun j _ => by ring
      _ = (∑ _j : W, n / 4) + (1 / 2) * (∑ j : W, v j) + (n / 2) * v i + y i := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          rfl
      _ = n ^ 2 / 4 + (n / 2) * v i + y i := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def, hsum_v]
          ring
  have hsum_y : ∑ i : W, y i = - ∑ j : W, v j ^ 2 := by
    calc ∑ i : W, ∑ j : W, U i j * v j
        = ∑ j : W, ∑ i : W, U i j * v j := Finset.sum_comm
      _ = ∑ j : W, (∑ i : W, (- U j i)) * v j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by rw [hU_skew j i, neg_mul]
      _ = - ∑ j : W, v j ^ 2 := by
          simp only [Finset.sum_neg_distrib, neg_mul]
          congr 1
          exact Finset.sum_congr rfl fun j _ => (sq (v j)).symm
  have hsum_vy : ∑ i : W, v i * y i = 0 := by
    have hswap : ∑ i : W, v i * y i = - ∑ i : W, v i * y i := by
      calc ∑ i : W, v i * (∑ j : W, U i j * v j)
          = ∑ i : W, ∑ j : W, v i * U i j * v j :=
            Finset.sum_congr rfl fun i _ => by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ j : W, ∑ i : W, v i * U i j * v j := Finset.sum_comm
        _ = ∑ j : W, ∑ i : W, (- (v j * U j i * v i)) :=
            Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
              rw [hU_skew j i]; ring
        _ = - ∑ j : W, v j * (∑ i : W, U j i * v i) := by
            simp only [Finset.sum_neg_distrib]
            congr 1
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  have hsum_ysq : ∑ i : W, y i ^ 2 ≤ (n ^ 2 / 4) * (∑ j : W, v j ^ 2) := by
    have hrow : ∀ i : W, y i ^ 2 ≤ (n / 4) * (∑ j : W, v j ^ 2) := fun i => by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset W) (fun j => U i j) v
      have hUsq_sum : ∑ j : W, U i j ^ 2 ≤ n / 4 := by
        calc ∑ j : W, U i j ^ 2 ≤ ∑ _j : W, (1 / 4 : ℝ) := Finset.sum_le_sum fun j _ => hU_sq i j
          _ = n / 4 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def]; ring
      exact le_trans hcs (mul_le_mul_of_nonneg_right hUsq_sum
        (Finset.sum_nonneg fun j _ => sq_nonneg (v j)))
    calc ∑ i : W, y i ^ 2 ≤ ∑ _i : W, (n / 4) * (∑ j : W, v j ^ 2) :=
          Finset.sum_le_sum fun i _ => hrow i
      _ = n * ((n / 4) * (∑ j : W, v j ^ 2)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def]
      _ = (n ^ 2 / 4) * (∑ j : W, v j ^ 2) := by ring
  have hWf_sq_sum : ∑ i : W, Wf i ^ 2 =
      n ^ 5 / 16 - (n ^ 2 / 4) * (∑ j : W, v j ^ 2) + ∑ i : W, y i ^ 2 := by
    calc ∑ i : W, Wf i ^ 2
        = ∑ i : W, (n ^ 2 / 4 + (n / 2) * v i + y i) ^ 2 :=
          Finset.sum_congr rfl fun i _ => by rw [hWf_eq i]
      _ = ∑ i : W, (n ^ 4 / 16 + (n ^ 3 / 4) * v i + (n ^ 2 / 2) * y i +
            (n ^ 2 / 4) * v i ^ 2 + n * (v i * y i) + y i ^ 2) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ _i : W, n ^ 4 / 16) + (n ^ 3 / 4) * (∑ i : W, v i) +
            (n ^ 2 / 2) * (∑ i : W, y i) + (n ^ 2 / 4) * (∑ i : W, v i ^ 2) +
            n * (∑ i : W, v i * y i) + ∑ i : W, y i ^ 2 := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = n ^ 5 / 16 - (n ^ 2 / 4) * (∑ j : W, v j ^ 2) + ∑ i : W, y i ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def,
            hsum_v, hsum_y, hsum_vy]
          ring
  linarith [hcard_le_Wf_sq, hWf_sq_sum, hsum_ysq]

end SmallBounds

/- ### Section 3: Marginal entropies, Gibbs inequality, and Markov-step bounds -/

private lemma sum_mul_tr_le {W : Type*} [Fintype W] {a : ℝ} (ha : 0 ≤ a)
    (tr : W → ℝ) (htr : ∑ x : W, tr x ≤ 1) :
    ∑ x : W, a * tr x ≤ a := by
  rw [← Finset.mul_sum]
  exact mul_le_of_le_one_right ha htr

section EntropyEngine

variable {W : Type*} [Fintype W] [DecidableEq W] (G : Digraph W) [DecidableRel G.Adj]

def d0Homs : Finset (Fin 10 → W) :=
  Finset.univ.filter (fun f => ∀ i j : Fin 10, D0.Adj i j → G.Adj (f i) (f j))

omit [DecidableEq W] in
lemma homCount_D0_eq : Digraph.homCount D0 G = (d0Homs G).card := by
  unfold Digraph.homCount
  let e : (D0 →g G) ≃ ↥(d0Homs G) :=
    { toFun := fun φ => ⟨φ.toFun, by
        simp only [d0Homs, Finset.mem_filter, Finset.mem_univ, true_and]
        intro i j hij; exact φ.map_adj' hij⟩
      invFun := fun f => ⟨f.1, fun {i j} hij => by
        have hf := f.2
        simp only [d0Homs, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        exact hf i j hij⟩
      left_inv := fun φ => by cases φ; rfl
      right_inv := fun f => by cases f; rfl }
  rw [Fintype.card_congr e, Fintype.card_coe]

noncomputable def hEnt (x : ℝ) : ℝ := - x * Real.log x

lemma hEnt_zero : hEnt 0 = 0 := by simp [hEnt]

lemma hEnt_one : hEnt 1 = 0 := by simp [hEnt]

lemma hEnt_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    hEnt (x * y) = x * hEnt y + y * hEnt x := by
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · simp [hEnt]
  · rcases eq_or_lt_of_le hy with rfl | hy_pos
    · simp [hEnt]
    · simp only [hEnt, Real.log_mul hx_pos.ne' hy_pos.ne']
      ring

lemma mul_hEnt_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    y * hEnt (x / y) = hEnt x - (x / y) * hEnt y := by
  have h1 := hEnt_mul (div_nonneg hx hy.le) hy.le
  rw [div_mul_cancel₀ x hy.ne'] at h1
  linarith

lemma gibbs_ineq {α : Type*} [Fintype α] (S : Finset α) (q : α → ℝ)
    (hq_nn : ∀ x, 0 ≤ q x) (hq_supp : ∀ x, x ∉ S → q x = 0)
    (hq_sum : ∑ x : α, q x = 1) :
    0 < S.card ∧ ∑ x : α, hEnt (q x) ≤ Real.log (S.card : ℝ) := by
  have hS_sum : ∑ x ∈ S, q x = 1 := by
    rw [← hq_sum]
    exact (Finset.sum_subset (Finset.subset_univ S) fun x _ hx => hq_supp x hx)
  have hS_pos : 0 < S.card := by
    by_contra h0
    have hSe : S = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hSe, Finset.sum_empty] at hS_sum
    norm_num at hS_sum
  refine ⟨hS_pos, ?_⟩
  have hSc_pos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr hS_pos
  have hent_eq : ∑ x : α, hEnt (q x) = ∑ x ∈ S, hEnt (q x) := by
    symm
    refine Finset.sum_subset (Finset.subset_univ S) fun x _ hx => ?_
    rw [hq_supp x hx, hEnt_zero]
  have hterm : ∀ x ∈ S, hEnt (q x) - q x * Real.log (S.card : ℝ) ≤ 1 / (S.card : ℝ) - q x := by
    intro x _
    rcases eq_or_lt_of_le (hq_nn x) with hq0 | hq_pos
    · rw [← hq0, hEnt_zero, zero_mul, sub_zero, sub_zero]
      exact div_nonneg zero_le_one hSc_pos.le
    · have ht_pos : 0 < (1 / (S.card : ℝ)) / q x := div_pos (div_pos one_pos hSc_pos) hq_pos
      have hlog := Real.log_le_sub_one_of_pos ht_pos
      rw [Real.log_div (div_pos one_pos hSc_pos).ne' hq_pos.ne', one_div, Real.log_inv] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hq_pos.le
      have hcancel : q x * ((S.card : ℝ)⁻¹ / q x - 1) = 1 / (S.card : ℝ) - q x := by
        field_simp [hq_pos.ne']
      rw [hcancel] at hmul
      dsimp [hEnt]
      linarith
  have hsum_le := Finset.sum_le_sum hterm
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul] at hsum_le
  rw [hS_sum, one_mul, mul_one_div_cancel hSc_pos.ne', sub_self] at hsum_le
  rw [hent_eq]
  linarith

noncomputable def p1 (i : Fin 10) (a : W) : ℝ :=
  (((d0Homs G).filter (fun f => f i = a)).card : ℝ) / ((d0Homs G).card : ℝ)

noncomputable def p2 (i j : Fin 10) (a b : W) : ℝ :=
  (((d0Homs G).filter (fun f => f i = a ∧ f j = b)).card : ℝ) / ((d0Homs G).card : ℝ)

noncomputable def H1 (i : Fin 10) : ℝ :=
  ∑ a : W, hEnt (p1 G i a)

noncomputable def H2 (i j : Fin 10) : ℝ :=
  ∑ p : W × W, hEnt (p2 G i j p.1 p.2)

lemma p1_nonneg (i : Fin 10) (a : W) : 0 ≤ p1 G i a :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma p2_nonneg (i j : Fin 10) (a b : W) : 0 ≤ p2 G i j a b :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma sum_p1 (hM : 0 < (d0Homs G).card) (i : Fin 10) :
    ∑ a : W, p1 G i a = 1 := by
  have hM_pos : (0 : ℝ) < ((d0Homs G).card : ℝ) := Nat.cast_pos.mpr hM
  unfold p1
  rw [← Finset.sum_div, ← Nat.cast_sum]
  have hpart : ∑ a : W, ((d0Homs G).filter (fun f => f i = a)).card = (d0Homs G).card := by
    have heq : d0Homs G = Finset.univ.biUnion (fun a : W => (d0Homs G).filter (fun f => f i = a)) := by
      ext f; simp
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset W))
        (fun a : W => (d0Homs G).filter (fun f => f i = a)) := by
      intro a1 _ a2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro f hf1 hf2
      simp only [Finset.mem_filter] at hf1 hf2
      exact hne (hf1.2.symm.trans hf2.2)
    conv_rhs => rw [heq, Finset.card_biUnion hdisj]
  rw [hpart, div_self hM_pos.ne']

lemma sum_p2_snd (i j : Fin 10) (a : W) :
    ∑ b : W, p2 G i j a b = p1 G i a := by
  unfold p2 p1
  rw [← Finset.sum_div, ← Nat.cast_sum]
  congr 2
  have heq : (d0Homs G).filter (fun f => f i = a) =
      Finset.univ.biUnion (fun b : W => (d0Homs G).filter (fun f => f i = a ∧ f j = b)) := by
    ext f; simp
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset W))
      (fun b : W => (d0Homs G).filter (fun f => f i = a ∧ f j = b)) := by
    intro b1 _ b2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro f hf1 hf2
    simp only [Finset.mem_filter] at hf1 hf2
    exact hne (hf1.2.2.symm.trans hf2.2.2)
  rw [heq, Finset.card_biUnion hdisj]

lemma sum_p2_fst (i j : Fin 10) (b : W) :
    ∑ a : W, p2 G i j a b = p1 G j b := by
  unfold p2 p1
  rw [← Finset.sum_div, ← Nat.cast_sum]
  congr 2
  have heq : (d0Homs G).filter (fun f => f j = b) =
      Finset.univ.biUnion (fun a : W => (d0Homs G).filter (fun f => f i = a ∧ f j = b)) := by
    ext f; simp [and_comm]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset W))
      (fun a : W => (d0Homs G).filter (fun f => f i = a ∧ f j = b)) := by
    intro a1 _ a2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro f hf1 hf2
    simp only [Finset.mem_filter] at hf1 hf2
    exact hne (hf1.2.1.symm.trans hf2.2.1)
  rw [heq, Finset.card_biUnion hdisj]

lemma p2_le_p1_fst (i j : Fin 10) (a b : W) :
    p2 G i j a b ≤ p1 G i a := by
  rw [← sum_p2_snd G i j a]
  exact Finset.single_le_sum (fun x _ => p2_nonneg G i j a x) (Finset.mem_univ b)

lemma p2_le_p1_snd (i j : Fin 10) (a b : W) :
    p2 G i j a b ≤ p1 G j b := by
  rw [← sum_p2_fst G i j b]
  exact Finset.single_le_sum (fun x _ => p2_nonneg G i j x b) (Finset.mem_univ a)

lemma p2_eq_zero_of_not_adj {i j : Fin 10} (hadj : D0.Adj i j) {a b : W} (hnot : ¬ G.Adj a b) :
    p2 G i j a b = 0 := by
  unfold p2
  have hemp : (d0Homs G).filter (fun f => f i = a ∧ f j = b) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro f hf
    simp only [d0Homs, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨hf_hom, rfl, rfl⟩ := hf
    exact hnot (hf_hom i j hadj)
  simp [hemp]

lemma H1_le_log_card (hM : 0 < (d0Homs G).card) (i : Fin 10) :
    H1 G i ≤ Real.log (Fintype.card W : ℝ) := by
  have h := (gibbs_ineq (Finset.univ : Finset W) (p1 G i) (p1_nonneg G i)
    (fun _ hx => absurd (Finset.mem_univ _) hx) (sum_p1 G hM i)).2
  simpa [H1, Finset.card_univ] using h

/- #### Lower bound `Real.log M <= E(D0)` via KL divergence against the Markov tree product -/

noncomputable def trOut (u v : Fin 10) (a b : W) : ℝ :=
  if p1 G u a = 0 then 0 else p2 G u v a b / p1 G u a

noncomputable def trIn (v u : Fin 10) (a b : W) : ℝ :=
  if p1 G u a = 0 then 0 else p2 G v u b a / p1 G u a

lemma trOut_nonneg (u v : Fin 10) (a b : W) : 0 ≤ trOut G u v a b := by
  dsimp [trOut]
  split_ifs
  · exact le_refl 0
  · exact div_nonneg (p2_nonneg G u v a b) (p1_nonneg G u a)

lemma trIn_nonneg (v u : Fin 10) (a b : W) : 0 ≤ trIn G v u a b := by
  dsimp [trIn]
  split_ifs
  · exact le_refl 0
  · exact div_nonneg (p2_nonneg G v u b a) (p1_nonneg G u a)

lemma sum_trOut_eq_one_of_ne_zero (u v : Fin 10) {a : W} (h0 : p1 G u a ≠ 0) :
    ∑ b : W, trOut G u v a b = 1 := by
  dsimp [trOut]
  simp only [h0, ↓reduceIte, ← Finset.sum_div, sum_p2_snd, div_self h0]

lemma sum_trIn_eq_one_of_ne_zero (v u : Fin 10) {a : W} (h0 : p1 G u a ≠ 0) :
    ∑ b : W, trIn G v u a b = 1 := by
  dsimp [trIn]
  simp only [h0, ↓reduceIte, ← Finset.sum_div, sum_p2_fst, div_self h0]

lemma sum_trOut_le_one (u v : Fin 10) (a : W) :
    ∑ b : W, trOut G u v a b ≤ 1 := by
  by_cases h0 : p1 G u a = 0
  · simp [trOut, h0]
  · exact (sum_trOut_eq_one_of_ne_zero G u v h0).le

lemma sum_trIn_le_one (v u : Fin 10) (a : W) :
    ∑ b : W, trIn G v u a b ≤ 1 := by
  by_cases h0 : p1 G u a = 0
  · simp [trIn, h0]
  · exact (sum_trIn_eq_one_of_ne_zero G v u h0).le

private noncomputable def treeQ (f : Fin 10 → W) : ℝ :=
  p1 G 4 (f 4) *
  trOut G 4 3 (f 4) (f 3) *
  trIn G 2 3 (f 3) (f 2) *
  trIn G 1 2 (f 2) (f 1) *
  trIn G 0 1 (f 1) (f 0) *
  trIn G 5 4 (f 4) (f 5) *
  trIn G 6 5 (f 5) (f 6) *
  trIn G 7 6 (f 6) (f 7) *
  trOut G 4 8 (f 4) (f 8) *
  trOut G 8 9 (f 8) (f 9)

private lemma sum_treeQ_le_one (hM : 0 < (d0Homs G).card) :
    ∑ f : Fin 10 → W, treeQ G f ≤ 1 := by
  let e10 : (Fin 10 → W) ≃ W × W × W × W × W × W × W × W × W × W :=
    { toFun := fun f => (f 4, f 3, f 2, f 1, f 0, f 5, f 6, f 7, f 8, f 9)
      invFun := fun t =>
        ![t.2.2.2.2.1, t.2.2.2.1, t.2.2.1, t.2.1, t.1,
          t.2.2.2.2.2.1, t.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.1,
          t.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2]
      left_inv := fun f => by ext i; fin_cases i <;> rfl
      right_inv := fun t => by
        rcases t with ⟨w4, w3, w2, w1, w0, w5, w6, w7, w8, w9⟩; rfl }
  rw [Fintype.sum_equiv e10 (treeQ G) (fun t =>
    p1 G 4 t.1 *
    trOut G 4 3 t.1 t.2.1 *
    trIn G 2 3 t.2.1 t.2.2.1 *
    trIn G 1 2 t.2.2.1 t.2.2.2.1 *
    trIn G 0 1 t.2.2.2.1 t.2.2.2.2.1 *
    trIn G 5 4 t.1 t.2.2.2.2.2.1 *
    trIn G 6 5 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 *
    trIn G 7 6 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2.1 *
    trOut G 4 8 t.1 t.2.2.2.2.2.2.2.2.1 *
    trOut G 8 9 t.2.2.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2.2.2) (fun _ => rfl)]
  simp only [Fintype.sum_prod_type]
  refine le_trans (Finset.sum_le_sum fun w4 _ => Finset.sum_le_sum fun w3 _ =>
    Finset.sum_le_sum fun w2 _ => Finset.sum_le_sum fun w1 _ =>
    Finset.sum_le_sum fun w0 _ => Finset.sum_le_sum fun w5 _ =>
    Finset.sum_le_sum fun w6 _ => Finset.sum_le_sum fun w7 _ =>
    Finset.sum_le_sum fun w8 _ => sum_mul_tr_le
      (by positivity [p1_nonneg G 4 w4, trOut_nonneg G 4 3 w4 w3,
            trIn_nonneg G 2 3 w3 w2, trIn_nonneg G 1 2 w2 w1,
            trIn_nonneg G 0 1 w1 w0, trIn_nonneg G 5 4 w4 w5,
            trIn_nonneg G 6 5 w5 w6, trIn_nonneg G 7 6 w6 w7,
            trOut_nonneg G 4 8 w4 w8])
      _ (sum_trOut_le_one G 8 9 w8)) ?_
  refine le_trans (Finset.sum_le_sum fun w4 _ => Finset.sum_le_sum fun w3 _ =>
    Finset.sum_le_sum fun w2 _ => Finset.sum_le_sum fun w1 _ =>
    Finset.sum_le_sum fun w0 _ => Finset.sum_le_sum fun w5 _ =>
    Finset.sum_le_sum fun w6 _ => Finset.sum_le_sum fun w7 _ =>
    sum_mul_tr_le
      (by positivity [p1_nonneg G 4 w4, trOut_nonneg G 4 3 w4 w3,
            trIn_nonneg G 2 3 w3 w2, trIn_nonneg G 1 2 w2 w1,
            trIn_nonneg G 0 1 w1 w0, trIn_nonneg G 5 4 w4 w5,
            trIn_nonneg G 6 5 w5 w6, trIn_nonneg G 7 6 w6 w7])
      _ (sum_trOut_le_one G 4 8 w4)) ?_
  refine le_trans (Finset.sum_le_sum fun w4 _ => Finset.sum_le_sum fun w3 _ =>
    Finset.sum_le_sum fun w2 _ => Finset.sum_le_sum fun w1 _ =>
    Finset.sum_le_sum fun w0 _ => Finset.sum_le_sum fun w5 _ =>
    Finset.sum_le_sum fun w6 _ =>
    sum_mul_tr_le
      (by positivity [p1_nonneg G 4 w4, trOut_nonneg G 4 3 w4 w3,
            trIn_nonneg G 2 3 w3 w2, trIn_nonneg G 1 2 w2 w1,
            trIn_nonneg G 0 1 w1 w0, trIn_nonneg G 5 4 w4 w5,
            trIn_nonneg G 6 5 w5 w6])
      _ (sum_trIn_le_one G 7 6 w6)) ?_
  refine le_trans (Finset.sum_le_sum fun w4 _ => Finset.sum_le_sum fun w3 _ =>
    Finset.sum_le_sum fun w2 _ => Finset.sum_le_sum fun w1 _ =>
    Finset.sum_le_sum fun w0 _ => Finset.sum_le_sum fun w5 _ =>
    sum_mul_tr_le
      (by positivity [p1_nonneg G 4 w4, trOut_nonneg G 4 3 w4 w3,
            trIn_nonneg G 2 3 w3 w2, trIn_nonneg G 1 2 w2 w1,
            trIn_nonneg G 0 1 w1 w0, trIn_nonneg G 5 4 w4 w5])
      _ (sum_trIn_le_one G 6 5 w5)) ?_
  refine le_trans (Finset.sum_le_sum fun w4 _ => Finset.sum_le_sum fun w3 _ =>
    Finset.sum_le_sum fun w2 _ => Finset.sum_le_sum fun w1 _ =>
    Finset.sum_le_sum fun w0 _ =>
    sum_mul_tr_le
      (by positivity [p1_nonneg G 4 w4, trOut_nonneg G 4 3 w4 w3,
            trIn_nonneg G 2 3 w3 w2, trIn_nonneg G 1 2 w2 w1,
            trIn_nonneg G 0 1 w1 w0])
      _ (sum_trIn_le_one G 5 4 w4)) ?_
  refine le_trans (Finset.sum_le_sum fun w4 _ => Finset.sum_le_sum fun w3 _ =>
    Finset.sum_le_sum fun w2 _ => Finset.sum_le_sum fun w1 _ =>
    sum_mul_tr_le
      (by positivity [p1_nonneg G 4 w4, trOut_nonneg G 4 3 w4 w3,
            trIn_nonneg G 2 3 w3 w2, trIn_nonneg G 1 2 w2 w1])
      _ (sum_trIn_le_one G 0 1 w1)) ?_
  refine le_trans (Finset.sum_le_sum fun w4 _ => Finset.sum_le_sum fun w3 _ =>
    Finset.sum_le_sum fun w2 _ =>
    sum_mul_tr_le
      (by positivity [p1_nonneg G 4 w4, trOut_nonneg G 4 3 w4 w3,
            trIn_nonneg G 2 3 w3 w2])
      _ (sum_trIn_le_one G 1 2 w2)) ?_
  refine le_trans (Finset.sum_le_sum fun w4 _ => Finset.sum_le_sum fun w3 _ =>
    sum_mul_tr_le (by positivity [p1_nonneg G 4 w4, trOut_nonneg G 4 3 w4 w3])
      _ (sum_trIn_le_one G 2 3 w3)) ?_
  refine le_trans (Finset.sum_le_sum fun w4 _ =>
    sum_mul_tr_le (p1_nonneg G 4 w4) _ (sum_trOut_le_one G 4 3 w4)) ?_
  exact (sum_p1 G hM 4).le

private lemma p1_pos_of_mem_d0Homs {f : Fin 10 → W} (hf : f ∈ d0Homs G) (i : Fin 10) :
    0 < p1 G i (f i) := by
  have hM : 0 < (d0Homs G).card := Finset.card_pos.mpr ⟨f, hf⟩
  have hmem : f ∈ (d0Homs G).filter (fun g => g i = f i) :=
    Finset.mem_filter.mpr ⟨hf, rfl⟩
  have hpos : 0 < ((d0Homs G).filter (fun g => g i = f i)).card :=
    Finset.card_pos.mpr ⟨f, hmem⟩
  exact div_pos (Nat.cast_pos.mpr hpos) (Nat.cast_pos.mpr hM)

private lemma p2_pos_of_mem_d0Homs {f : Fin 10 → W} (hf : f ∈ d0Homs G) (i j : Fin 10) :
    0 < p2 G i j (f i) (f j) := by
  have hM : 0 < (d0Homs G).card := Finset.card_pos.mpr ⟨f, hf⟩
  have hmem : f ∈ (d0Homs G).filter (fun g => g i = f i ∧ g j = f j) :=
    Finset.mem_filter.mpr ⟨hf, rfl, rfl⟩
  have hpos : 0 < ((d0Homs G).filter (fun g => g i = f i ∧ g j = f j)).card :=
    Finset.card_pos.mpr ⟨f, hmem⟩
  exact div_pos (Nat.cast_pos.mpr hpos) (Nat.cast_pos.mpr hM)

private lemma sum_neg_log_p1 (i : Fin 10) :
    ∑ f ∈ d0Homs G, (- (1 / ((d0Homs G).card : ℝ)) * Real.log (p1 G i (f i))) = H1 G i := by
  have heq : d0Homs G = Finset.univ.biUnion (fun a : W => (d0Homs G).filter (fun f => f i = a)) := by
    ext f; simp
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset W))
      (fun a : W => (d0Homs G).filter (fun f => f i = a)) := by
    intro a1 _ a2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro f hf1 hf2
    simp only [Finset.mem_filter] at hf1 hf2
    exact hne (hf1.2.symm.trans hf2.2)
  have hbi := Finset.sum_biUnion hdisj
    (f := fun f => (- (1 / ((d0Homs G).card : ℝ)) * Real.log (p1 G i (f i))))
  rw [← heq] at hbi
  rw [hbi]
  unfold H1
  refine Finset.sum_congr rfl fun a _ => ?_
  have hcongr : ∑ f ∈ (d0Homs G).filter (fun f => f i = a),
      (- (1 / ((d0Homs G).card : ℝ)) * Real.log (p1 G i (f i))) =
      ∑ _f ∈ (d0Homs G).filter (fun f => f i = a),
        (- (1 / ((d0Homs G).card : ℝ)) * Real.log (p1 G i a)) := by
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [(Finset.mem_filter.mp hf).2]
  rw [hcongr, Finset.sum_const, nsmul_eq_mul]
  unfold p1 hEnt
  ring

private lemma sum_neg_log_p2 (i j : Fin 10) :
    ∑ f ∈ d0Homs G, (- (1 / ((d0Homs G).card : ℝ)) * Real.log (p2 G i j (f i) (f j))) =
      H2 G i j := by
  have heq : d0Homs G = Finset.univ.biUnion
      (fun p : W × W => (d0Homs G).filter (fun f => f i = p.1 ∧ f j = p.2)) := by
    ext f; simp
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (W × W)))
      (fun p : W × W => (d0Homs G).filter (fun f => f i = p.1 ∧ f j = p.2)) := by
    intro p1 _ p2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro f hf1 hf2
    simp only [Finset.mem_filter] at hf1 hf2
    exact hne (Prod.ext (hf1.2.1.symm.trans hf2.2.1) (hf1.2.2.symm.trans hf2.2.2))
  have hbi := Finset.sum_biUnion hdisj
    (f := fun f => (- (1 / ((d0Homs G).card : ℝ)) * Real.log (p2 G i j (f i) (f j))))
  rw [← heq] at hbi
  rw [hbi]
  unfold H2
  refine Finset.sum_congr rfl fun p _ => ?_
  have hcongr : ∑ f ∈ (d0Homs G).filter (fun f => f i = p.1 ∧ f j = p.2),
      (- (1 / ((d0Homs G).card : ℝ)) * Real.log (p2 G i j (f i) (f j))) =
      ∑ _f ∈ (d0Homs G).filter (fun f => f i = p.1 ∧ f j = p.2),
        (- (1 / ((d0Homs G).card : ℝ)) * Real.log (p2 G i j p.1 p.2)) := by
    refine Finset.sum_congr rfl fun f hf => ?_
    obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp hf
    rw [h1, h2]
  rw [hcongr, Finset.sum_const, nsmul_eq_mul]
  unfold p2 hEnt
  ring

lemma log_homCount_le_spider_ent (hM : 0 < (d0Homs G).card) :
    Real.log ((d0Homs G).card : ℝ) ≤
      H2 G 0 1 + H2 G 1 2 + H2 G 2 3 + H2 G 4 3 + H2 G 5 4 +
      H2 G 6 5 + H2 G 7 6 + H2 G 4 8 + H2 G 8 9 -
      H1 G 1 - H1 G 2 - H1 G 3 - 2 * H1 G 4 - H1 G 5 - H1 G 6 - H1 G 8 := by
  set M : ℝ := ((d0Homs G).card : ℝ) with hM_def
  have hM_pos : 0 < M := Nat.cast_pos.mpr hM
  have hpoint : ∀ f ∈ d0Homs G,
      (1 / M) * Real.log M -
      ((1 / M) * (- Real.log (treeQ G f))) ≤ treeQ G f - 1 / M := by
    intro f hf
    have hp4 := p1_pos_of_mem_d0Homs G hf 4
    have hp3 := p1_pos_of_mem_d0Homs G hf 3
    have hp2 := p1_pos_of_mem_d0Homs G hf 2
    have hp1 := p1_pos_of_mem_d0Homs G hf 1
    have hp5 := p1_pos_of_mem_d0Homs G hf 5
    have hp6 := p1_pos_of_mem_d0Homs G hf 6
    have hp8 := p1_pos_of_mem_d0Homs G hf 8
    have hq_pos : 0 < treeQ G f := by
      unfold treeQ trOut trIn
      simp only [hp4.ne', hp3.ne', hp2.ne', hp1.ne', hp5.ne', hp6.ne', hp8.ne', ↓reduceIte]
      positivity [hp4, hp3, hp2, hp1, hp5, hp6, hp8,
        p2_pos_of_mem_d0Homs G hf 4 3, p2_pos_of_mem_d0Homs G hf 2 3,
        p2_pos_of_mem_d0Homs G hf 1 2, p2_pos_of_mem_d0Homs G hf 0 1,
        p2_pos_of_mem_d0Homs G hf 5 4, p2_pos_of_mem_d0Homs G hf 6 5,
        p2_pos_of_mem_d0Homs G hf 7 6, p2_pos_of_mem_d0Homs G hf 4 8,
        p2_pos_of_mem_d0Homs G hf 8 9]
    have hlog := Real.log_le_sub_one_of_pos (mul_pos hM_pos hq_pos)
    rw [Real.log_mul hM_pos.ne' hq_pos.ne'] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (div_pos one_pos hM_pos).le
    have hcancel : (1 / M) * (M * treeQ G f - 1) = treeQ G f - 1 / M := by
      field_simp [hM_pos.ne']
    rw [hcancel] at hmul
    linarith
  have hlog_expand : ∀ f ∈ d0Homs G,
      (1 / M) * (- Real.log (treeQ G f)) =
      (- (1 / M) * Real.log (p2 G 0 1 (f 0) (f 1))) +
      (- (1 / M) * Real.log (p2 G 1 2 (f 1) (f 2))) +
      (- (1 / M) * Real.log (p2 G 2 3 (f 2) (f 3))) +
      (- (1 / M) * Real.log (p2 G 4 3 (f 4) (f 3))) +
      (- (1 / M) * Real.log (p2 G 5 4 (f 5) (f 4))) +
      (- (1 / M) * Real.log (p2 G 6 5 (f 6) (f 5))) +
      (- (1 / M) * Real.log (p2 G 7 6 (f 7) (f 6))) +
      (- (1 / M) * Real.log (p2 G 4 8 (f 4) (f 8))) +
      (- (1 / M) * Real.log (p2 G 8 9 (f 8) (f 9))) -
      (- (1 / M) * Real.log (p1 G 1 (f 1))) -
      (- (1 / M) * Real.log (p1 G 2 (f 2))) -
      (- (1 / M) * Real.log (p1 G 3 (f 3))) -
      (- (1 / M) * Real.log (p1 G 4 (f 4))) -
      (- (1 / M) * Real.log (p1 G 4 (f 4))) -
      (- (1 / M) * Real.log (p1 G 5 (f 5))) -
      (- (1 / M) * Real.log (p1 G 6 (f 6))) -
      (- (1 / M) * Real.log (p1 G 8 (f 8))) := by
    intro f hf
    have hp4 := (p1_pos_of_mem_d0Homs G hf 4).ne'
    have hp3 := (p1_pos_of_mem_d0Homs G hf 3).ne'
    have hp2 := (p1_pos_of_mem_d0Homs G hf 2).ne'
    have hp1 := (p1_pos_of_mem_d0Homs G hf 1).ne'
    have hp5 := (p1_pos_of_mem_d0Homs G hf 5).ne'
    have hp6 := (p1_pos_of_mem_d0Homs G hf 6).ne'
    have hp8 := (p1_pos_of_mem_d0Homs G hf 8).ne'
    have h43 := (p2_pos_of_mem_d0Homs G hf 4 3).ne'
    have h23 := (p2_pos_of_mem_d0Homs G hf 2 3).ne'
    have h12 := (p2_pos_of_mem_d0Homs G hf 1 2).ne'
    have h01 := (p2_pos_of_mem_d0Homs G hf 0 1).ne'
    have h54 := (p2_pos_of_mem_d0Homs G hf 5 4).ne'
    have h65 := (p2_pos_of_mem_d0Homs G hf 6 5).ne'
    have h76 := (p2_pos_of_mem_d0Homs G hf 7 6).ne'
    have h48 := (p2_pos_of_mem_d0Homs G hf 4 8).ne'
    have h89 := (p2_pos_of_mem_d0Homs G hf 8 9).ne'
    have htr43 : trOut G 4 3 (f 4) (f 3) ≠ 0 := by simp [trOut, hp4, h43]
    have htr23 : trIn G 2 3 (f 3) (f 2) ≠ 0 := by simp [trIn, hp3, h23]
    have htr12 : trIn G 1 2 (f 2) (f 1) ≠ 0 := by simp [trIn, hp2, h12]
    have htr01 : trIn G 0 1 (f 1) (f 0) ≠ 0 := by simp [trIn, hp1, h01]
    have htr54 : trIn G 5 4 (f 4) (f 5) ≠ 0 := by simp [trIn, hp4, h54]
    have htr65 : trIn G 6 5 (f 5) (f 6) ≠ 0 := by simp [trIn, hp5, h65]
    have htr76 : trIn G 7 6 (f 6) (f 7) ≠ 0 := by simp [trIn, hp6, h76]
    have htr48 : trOut G 4 8 (f 4) (f 8) ≠ 0 := by simp [trOut, hp4, h48]
    have htr89 : trOut G 8 9 (f 8) (f 9) ≠ 0 := by simp [trOut, hp8, h89]
    unfold treeQ
    rw [Real.log_mul (by positivity) htr89,
        Real.log_mul (by positivity) htr48,
        Real.log_mul (by positivity) htr76,
        Real.log_mul (by positivity) htr65,
        Real.log_mul (by positivity) htr54,
        Real.log_mul (by positivity) htr01,
        Real.log_mul (by positivity) htr12,
        Real.log_mul (by positivity) htr23,
        Real.log_mul hp4 htr43]
    simp only [trOut, trIn, hp4, hp3, hp2, hp1, hp5, hp6, hp8, ↓reduceIte]
    rw [Real.log_div h43 hp4, Real.log_div h23 hp3, Real.log_div h12 hp2,
        Real.log_div h01 hp1, Real.log_div h54 hp4, Real.log_div h65 hp5,
        Real.log_div h76 hp6, Real.log_div h48 hp4, Real.log_div h89 hp8]
    ring
  have hsum_le := Finset.sum_le_sum hpoint
  have hsum_Q_sub : ∑ f ∈ d0Homs G, treeQ G f ≤ 1 := by
    refine le_trans (Finset.sum_le_univ_sum_of_nonneg fun f => ?_) (sum_treeQ_le_one G hM)
    unfold treeQ
    positivity [p1_nonneg G 4 (f 4), trOut_nonneg G 4 3 (f 4) (f 3),
      trIn_nonneg G 2 3 (f 3) (f 2), trIn_nonneg G 1 2 (f 2) (f 1),
      trIn_nonneg G 0 1 (f 1) (f 0), trIn_nonneg G 5 4 (f 4) (f 5),
      trIn_nonneg G 6 5 (f 5) (f 6), trIn_nonneg G 7 6 (f 6) (f 7),
      trOut_nonneg G 4 8 (f 4) (f 8), trOut_nonneg G 8 9 (f 8) (f 9)]
  have hsum_rhs : ∑ f ∈ d0Homs G, (treeQ G f - 1 / M) ≤ 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← hM_def,
      mul_one_div_cancel hM_pos.ne']
    linarith [hsum_Q_sub]
  have hsum_lhs : ∑ f ∈ d0Homs G,
      ((1 / M) * Real.log M - (1 / M) * (- Real.log (treeQ G f))) =
      Real.log M -
      (H2 G 0 1 + H2 G 1 2 + H2 G 2 3 + H2 G 4 3 + H2 G 5 4 +
       H2 G 6 5 + H2 G 7 6 + H2 G 4 8 + H2 G 8 9 -
       H1 G 1 - H1 G 2 - H1 G 3 - 2 * H1 G 4 - H1 G 5 - H1 G 6 - H1 G 8) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← hM_def,
      ← mul_assoc, mul_one_div_cancel hM_pos.ne', one_mul]
    rw [Finset.sum_congr rfl hlog_expand]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hM_def,
      sum_neg_log_p2, sum_neg_log_p1]
    ring
  linarith [hsum_le, hsum_rhs, hsum_lhs]

/- #### Conditional Markov-step PMF builder (`CondPMF`) -/

structure CondPMF (α : Type*) [Fintype α] (h : Fin 10) where
  q : W → α → ℝ
  supp : W → Finset α
  nonneg : ∀ b x, 0 ≤ q b x
  zero_of_not_mem : ∀ b x, x ∉ supp b → q b x = 0
  sum_eq : ∀ b, p1 G h b ≠ 0 → ∑ x : α, q b x = 1

noncomputable def CondPMF.ent {α : Type*} [Fintype α] {h : Fin 10} (C : CondPMF G α h) : ℝ :=
  ∑ b : W, p1 G h b * (∑ x : α, hEnt (C.q b x))

def CondPMF.HasMarg {α : Type*} [Fintype α] {h : Fin 10}
    (C : CondPMF G α h) (ev : α → W) (u : Fin 10) : Prop :=
  ∀ c : W, ∑ b : W, p1 G h b * (∑ x : α, if ev x = c then C.q b x else 0) = p1 G u c

lemma CondPMF.p1_ne_zero_of_q_ne_zero {α : Type*} [Fintype α] {h u : Fin 10}
    {C : CondPMF G α h} {ev : α → W} (hm : C.HasMarg G ev u)
    {b : W} (hb : p1 G h b ≠ 0) {x : α} (hx : C.q b x ≠ 0) :
    p1 G u (ev x) ≠ 0 := by
  have hb_pos : 0 < p1 G h b := lt_of_le_of_ne (p1_nonneg G h b) (Ne.symm hb)
  have hx_pos : 0 < C.q b x := lt_of_le_of_ne (C.nonneg b x) (Ne.symm hx)
  have hpos : 0 < p1 G u (ev x) := by
    rw [← hm (ev x)]
    refine lt_of_lt_of_le (mul_pos hb_pos hx_pos) ?_
    have h1 : C.q b x ≤ ∑ x' : α, if ev x' = ev x then C.q b x' else 0 := by
      have := Finset.single_le_sum
        (f := fun x' => if ev x' = ev x then C.q b x' else 0)
        (fun x' _ => by split_ifs; exact C.nonneg b x'; exact le_refl 0)
        (Finset.mem_univ x)
      simpa using this
    refine le_trans (mul_le_mul_of_nonneg_left h1 hb_pos.le) ?_
    exact Finset.single_le_sum
      (f := fun b' => p1 G h b' * ∑ x' : α, if ev x' = ev x then C.q b' x' else 0)
      (fun b' _ => mul_nonneg (p1_nonneg G h b')
        (Finset.sum_nonneg fun x' _ => by split_ifs; exact C.nonneg b' x'; exact le_refl 0))
      (Finset.mem_univ b)
  exact hpos.ne'

noncomputable def condBase (h : Fin 10) : CondPMF G W h where
  q b x := if x = b ∧ p1 G h b ≠ 0 then 1 else 0
  supp b := {b}
  nonneg b x := by split_ifs <;> norm_num
  zero_of_not_mem b x hx := by
    rw [Finset.mem_singleton] at hx
    simp [hx]
  sum_eq b hb := by
    simp [hb]

lemma condBase_ent (h : Fin 10) : (condBase G h).ent = 0 := by
  unfold CondPMF.ent condBase
  refine Finset.sum_eq_zero fun b _ => ?_
  suffices ∑ x : W, hEnt (if x = b ∧ p1 G h b ≠ 0 then (1 : ℝ) else 0) = 0 by
    rw [this, mul_zero]
  refine Finset.sum_eq_zero fun x _ => ?_
  split_ifs <;> simp [hEnt]

lemma condBase_hasMarg (h : Fin 10) : (condBase G h).HasMarg G id h := by
  intro c
  unfold condBase
  have hinner : ∀ b : W,
      (∑ x : W, if id x = c then (if x = b ∧ p1 G h b ≠ 0 then (1 : ℝ) else 0) else 0) =
      if b = c ∧ p1 G h b ≠ 0 then 1 else 0 := by
    intro b
    rw [Finset.sum_eq_single c]
    · rcases eq_or_ne b c with rfl | hbc
      · simp
      · have hcb : c ≠ b := hbc.symm
        simp [hbc, hcb]
    · intro x _ hxc; simp [hxc]
    · intro hc; exact absurd (Finset.mem_univ c) hc
  simp only [hinner]
  rw [Finset.sum_eq_single c]
  · by_cases hp : p1 G h c = 0 <;> simp [hp]
  · intro b _ hbc; simp [hbc]
  · intro hc; exact absurd (Finset.mem_univ c) hc

noncomputable def stepOut {α : Type*} [Fintype α] {h u v : Fin 10}
    (C : CondPMF G α h) (ev : α → W) (hm : C.HasMarg G ev u) (hadj : D0.Adj u v) :
    CondPMF G (α × W) h where
  q b p := C.q b p.1 * trOut G u v (ev p.1) p.2
  supp b := (C.supp b ×ˢ Finset.univ).filter (fun p => G.Adj (ev p.1) p.2)
  nonneg b p := mul_nonneg (C.nonneg b p.1) (trOut_nonneg G u v (ev p.1) p.2)
  zero_of_not_mem b p hp := by
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, not_and] at hp
    by_cases hx : p.1 ∈ C.supp b
    · have hnot := hp hx
      have hp2z := p2_eq_zero_of_not_adj G hadj hnot
      simp [trOut, hp2z]
    · rw [C.zero_of_not_mem b p.1 hx, zero_mul]
  sum_eq b hb := by
    rw [Fintype.sum_prod_type]
    have hrow : ∀ x : α, ∑ d : W, C.q b x * trOut G u v (ev x) d = C.q b x := by
      intro x
      by_cases hq : C.q b x = 0
      · simp [hq]
      · rw [← Finset.mul_sum,
          sum_trOut_eq_one_of_ne_zero G u v (C.p1_ne_zero_of_q_ne_zero G hm hb hq), mul_one]
    simp only [hrow]
    exact C.sum_eq b hb

lemma stepOut_hasMarg_fst {α : Type*} [Fintype α] {h u v w : Fin 10}
    (C : CondPMF G α h) (ev : α → W) (hm : C.HasMarg G ev u) (hadj : D0.Adj u v)
    {ev' : α → W} (hm' : C.HasMarg G ev' w) :
    (stepOut G C ev hm hadj).HasMarg G (fun p => ev' p.1) w := by
  intro c
  rw [← hm' c]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : p1 G h b = 0
  · simp [hb]
  · congr 1
    dsimp [stepOut]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hev : ev' x = c
    · simp only [hev, ↓reduceIte]
      by_cases hq : C.q b x = 0
      · simp [hq]
      · rw [← Finset.mul_sum,
          sum_trOut_eq_one_of_ne_zero G u v (C.p1_ne_zero_of_q_ne_zero G hm hb hq), mul_one]
    · simp [hev]

lemma stepOut_hasMarg_snd {α : Type*} [Fintype α] {h u v : Fin 10}
    (C : CondPMF G α h) (ev : α → W) (hm : C.HasMarg G ev u) (hadj : D0.Adj u v) :
    (stepOut G C ev hm hadj).HasMarg G Prod.snd v := by
  intro d
  dsimp [stepOut]
  have hinner : ∀ b : W,
      (∑ p : α × W, if p.2 = d then C.q b p.1 * trOut G u v (ev p.1) p.2 else 0) =
      ∑ c : W, (∑ x : α, if ev x = c then C.q b x else 0) * trOut G u v c d := by
    intro b
    rw [Fintype.sum_prod_type]
    have h1 : ∀ x : α,
        (∑ y : W, if y = d then C.q b x * trOut G u v (ev x) y else 0) =
        C.q b x * trOut G u v (ev x) d := fun x => by simp
    simp only [h1]
    symm
    calc ∑ c : W, (∑ x : α, if ev x = c then C.q b x else 0) * trOut G u v c d
        = ∑ c : W, ∑ x : α, (if ev x = c then C.q b x * trOut G u v c d else 0) :=
          Finset.sum_congr rfl fun c _ => by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
      _ = ∑ x : α, ∑ c : W, (if ev x = c then C.q b x * trOut G u v c d else 0) :=
          Finset.sum_comm
      _ = ∑ x : α, C.q b x * trOut G u v (ev x) d :=
          Finset.sum_congr rfl fun x _ => by simp
  simp only [hinner]
  calc ∑ b : W, p1 G h b * ∑ c : W, (∑ x : α, if ev x = c then C.q b x else 0) * trOut G u v c d
      = ∑ b : W, ∑ c : W, p1 G h b * (∑ x : α, if ev x = c then C.q b x else 0) * trOut G u v c d :=
        Finset.sum_congr rfl fun b _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
    _ = ∑ c : W, (∑ b : W, p1 G h b * (∑ x : α, if ev x = c then C.q b x else 0)) *
          trOut G u v c d := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => (Finset.sum_mul _ _ _).symm
    _ = ∑ c : W, p1 G u c * trOut G u v c d :=
        Finset.sum_congr rfl fun c _ => by rw [hm c]
    _ = ∑ c : W, p2 G u v c d := by
        refine Finset.sum_congr rfl fun c _ => ?_
        dsimp [trOut]
        by_cases h0 : p1 G u c = 0
        · have hp2z : p2 G u v c d = 0 :=
            le_antisymm (h0 ▸ p2_le_p1_fst G u v c d) (p2_nonneg G u v c d)
          simp [h0, hp2z]
        · simp [h0, mul_div_cancel₀ _ h0]
    _ = p1 G v d := sum_p2_fst G u v d

lemma stepOut_ent {α : Type*} [Fintype α] {h u v : Fin 10}
    (C : CondPMF G α h) (ev : α → W) (hm : C.HasMarg G ev u) (hadj : D0.Adj u v) :
    (stepOut G C ev hm hadj).ent = C.ent + H2 G u v - H1 G u := by
  unfold CondPMF.ent stepOut
  have hrow : ∀ b : W, p1 G h b * (∑ p : α × W, hEnt (C.q b p.1 * trOut G u v (ev p.1) p.2)) =
      p1 G h b * (∑ x : α, hEnt (C.q b x)) +
      ∑ c : W, p1 G h b * (∑ x : α, if ev x = c then C.q b x else 0) *
        (if p1 G u c = 0 then 0 else ((∑ d : W, hEnt (p2 G u v c d)) - hEnt (p1 G u c)) / p1 G u c) := by
    intro b
    by_cases hb : p1 G h b = 0
    · simp [hb]
    · rw [Fintype.sum_prod_type]
      have hx_eq : ∀ x : α,
          ∑ d : W, hEnt (C.q b x * trOut G u v (ev x) d) =
          hEnt (C.q b x) + C.q b x *
            (if p1 G u (ev x) = 0 then 0
             else ((∑ d : W, hEnt (p2 G u v (ev x) d)) - hEnt (p1 G u (ev x))) / p1 G u (ev x)) := by
        intro x
        by_cases hq : C.q b x = 0
        · simp [hq, hEnt_zero]
        · have hpu_ne := C.p1_ne_zero_of_q_ne_zero G hm hb hq
          have hpu_pos : 0 < p1 G u (ev x) := lt_of_le_of_ne (p1_nonneg G u (ev x)) (Ne.symm hpu_ne)
          have h1 : ∀ d : W, hEnt (C.q b x * trOut G u v (ev x) d) =
              C.q b x * hEnt (trOut G u v (ev x) d) + trOut G u v (ev x) d * hEnt (C.q b x) :=
            fun d => hEnt_mul (C.nonneg b x) (trOut_nonneg G u v (ev x) d)
          simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
            sum_trOut_eq_one_of_ne_zero G u v hpu_ne, one_mul, hpu_ne, ↓reduceIte]
          have h2 : ∀ d : W, hEnt (trOut G u v (ev x) d) =
              (hEnt (p2 G u v (ev x) d) - (p2 G u v (ev x) d / p1 G u (ev x)) * hEnt (p1 G u (ev x))) /
              p1 G u (ev x) := by
            intro d
            dsimp [trOut]
            simp only [hpu_ne, ↓reduceIte]
            have hmdiv := mul_hEnt_div (p2_nonneg G u v (ev x) d) hpu_pos
            exact (eq_div_iff hpu_ne).mpr (by linarith)
          have hsum_d : ∑ d : W, hEnt (trOut G u v (ev x) d) =
              ((∑ d : W, hEnt (p2 G u v (ev x) d)) - hEnt (p1 G u (ev x))) / p1 G u (ev x) := by
            rw [Finset.sum_congr rfl fun d _ => h2 d, ← Finset.sum_div, Finset.sum_sub_distrib,
              ← Finset.sum_mul, ← Finset.sum_div, sum_p2_snd, div_self hpu_ne, one_mul]
          rw [hsum_d]
          ring
      simp only [hx_eq, Finset.sum_add_distrib, mul_add]
      congr 1
      let g : W → ℝ := fun c =>
        if p1 G u c = 0 then 0 else ((∑ d : W, hEnt (p2 G u v c d)) - hEnt (p1 G u c)) / p1 G u c
      change p1 G h b * ∑ x : α, C.q b x * g (ev x) =
        ∑ c : W, p1 G h b * (∑ x : α, if ev x = c then C.q b x else 0) * g c
      rw [Finset.mul_sum]
      symm
      calc ∑ c : W, p1 G h b * (∑ x : α, if ev x = c then C.q b x else 0) * g c
          = ∑ c : W, ∑ x : α, (if ev x = c then p1 G h b * (C.q b x * g c) else 0) :=
            Finset.sum_congr rfl fun c _ => by
              rw [Finset.mul_sum, Finset.sum_mul]
              exact Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
        _ = ∑ x : α, ∑ c : W, (if ev x = c then p1 G h b * (C.q b x * g c) else 0) :=
            Finset.sum_comm
        _ = ∑ x : α, p1 G h b * (C.q b x * g (ev x)) :=
            Finset.sum_congr rfl fun x _ => by simp
  simp only [hrow, Finset.sum_add_distrib]
  have hH2 : H2 G u v = ∑ c : W, ∑ d : W, hEnt (p2 G u v c d) := by
    unfold H2
    rw [Fintype.sum_prod_type]
  have htele : ∑ b : W, ∑ c : W, p1 G h b * (∑ x : α, if ev x = c then C.q b x else 0) *
      (if p1 G u c = 0 then 0 else ((∑ d : W, hEnt (p2 G u v c d)) - hEnt (p1 G u c)) / p1 G u c) =
      H2 G u v - H1 G u := by
    rw [Finset.sum_comm]
    calc ∑ c : W, ∑ b : W, p1 G h b * (∑ x : α, if ev x = c then C.q b x else 0) *
            (if p1 G u c = 0 then 0
             else ((∑ d : W, hEnt (p2 G u v c d)) - hEnt (p1 G u c)) / p1 G u c)
        = ∑ c : W, p1 G u c *
            (if p1 G u c = 0 then 0
             else ((∑ d : W, hEnt (p2 G u v c d)) - hEnt (p1 G u c)) / p1 G u c) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [← Finset.sum_mul, hm c]
      _ = ∑ c : W, ((∑ d : W, hEnt (p2 G u v c d)) - hEnt (p1 G u c)) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          by_cases h0 : p1 G u c = 0
          · have hd0 : ∀ d : W, hEnt (p2 G u v c d) = 0 := fun d => by
              have : p2 G u v c d = 0 :=
                le_antisymm (h0 ▸ p2_le_p1_fst G u v c d) (p2_nonneg G u v c d)
              rw [this, hEnt_zero]
            simp [h0, hd0, hEnt_zero]
          · simp [h0, mul_div_cancel₀ _ h0]
      _ = H2 G u v - H1 G u := by
          rw [Finset.sum_sub_distrib, hH2]
          rfl
  rw [htele]
  ring

noncomputable def stepIn {α : Type*} [Fintype α] {h v u : Fin 10}
    (C : CondPMF G α h) (ev : α → W) (hm : C.HasMarg G ev u) (hadj : D0.Adj v u) :
    CondPMF G (α × W) h where
  q b p := C.q b p.1 * trIn G v u (ev p.1) p.2
  supp b := (C.supp b ×ˢ Finset.univ).filter (fun p => G.Adj p.2 (ev p.1))
  nonneg b p := mul_nonneg (C.nonneg b p.1) (trIn_nonneg G v u (ev p.1) p.2)
  zero_of_not_mem b p hp := by
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, not_and] at hp
    by_cases hx : p.1 ∈ C.supp b
    · have hnot := hp hx
      have hp2z := p2_eq_zero_of_not_adj G hadj hnot
      simp [trIn, hp2z]
    · rw [C.zero_of_not_mem b p.1 hx, zero_mul]
  sum_eq b hb := by
    rw [Fintype.sum_prod_type]
    have hrow : ∀ x : α, ∑ d : W, C.q b x * trIn G v u (ev x) d = C.q b x := by
      intro x
      by_cases hq : C.q b x = 0
      · simp [hq]
      · rw [← Finset.mul_sum,
          sum_trIn_eq_one_of_ne_zero G v u (C.p1_ne_zero_of_q_ne_zero G hm hb hq), mul_one]
    simp only [hrow]
    exact C.sum_eq b hb

lemma stepIn_hasMarg_fst {α : Type*} [Fintype α] {h v u w : Fin 10}
    (C : CondPMF G α h) (ev : α → W) (hm : C.HasMarg G ev u) (hadj : D0.Adj v u)
    {ev' : α → W} (hm' : C.HasMarg G ev' w) :
    (stepIn G C ev hm hadj).HasMarg G (fun p => ev' p.1) w := by
  intro c
  rw [← hm' c]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : p1 G h b = 0
  · simp [hb]
  · congr 1
    dsimp [stepIn]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hev : ev' x = c
    · simp only [hev, ↓reduceIte]
      by_cases hq : C.q b x = 0
      · simp [hq]
      · rw [← Finset.mul_sum,
          sum_trIn_eq_one_of_ne_zero G v u (C.p1_ne_zero_of_q_ne_zero G hm hb hq), mul_one]
    · simp [hev]

lemma stepIn_hasMarg_snd {α : Type*} [Fintype α] {h v u : Fin 10}
    (C : CondPMF G α h) (ev : α → W) (hm : C.HasMarg G ev u) (hadj : D0.Adj v u) :
    (stepIn G C ev hm hadj).HasMarg G Prod.snd v := by
  intro d
  dsimp [stepIn]
  have hinner : ∀ b : W,
      (∑ p : α × W, if p.2 = d then C.q b p.1 * trIn G v u (ev p.1) p.2 else 0) =
      ∑ c : W, (∑ x : α, if ev x = c then C.q b x else 0) * trIn G v u c d := by
    intro b
    rw [Fintype.sum_prod_type]
    have h1 : ∀ x : α,
        (∑ y : W, if y = d then C.q b x * trIn G v u (ev x) y else 0) =
        C.q b x * trIn G v u (ev x) d := fun x => by simp
    simp only [h1]
    symm
    calc ∑ c : W, (∑ x : α, if ev x = c then C.q b x else 0) * trIn G v u c d
        = ∑ c : W, ∑ x : α, (if ev x = c then C.q b x * trIn G v u c d else 0) :=
          Finset.sum_congr rfl fun c _ => by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
      _ = ∑ x : α, ∑ c : W, (if ev x = c then C.q b x * trIn G v u c d else 0) :=
          Finset.sum_comm
      _ = ∑ x : α, C.q b x * trIn G v u (ev x) d :=
          Finset.sum_congr rfl fun x _ => by simp
  simp only [hinner]
  calc ∑ b : W, p1 G h b * ∑ c : W, (∑ x : α, if ev x = c then C.q b x else 0) * trIn G v u c d
      = ∑ b : W, ∑ c : W, p1 G h b * (∑ x : α, if ev x = c then C.q b x else 0) * trIn G v u c d :=
        Finset.sum_congr rfl fun b _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
    _ = ∑ c : W, (∑ b : W, p1 G h b * (∑ x : α, if ev x = c then C.q b x else 0)) *
          trIn G v u c d := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => (Finset.sum_mul _ _ _).symm
    _ = ∑ c : W, p1 G u c * trIn G v u c d :=
        Finset.sum_congr rfl fun c _ => by rw [hm c]
    _ = ∑ c : W, p2 G v u d c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        dsimp [trIn]
        by_cases h0 : p1 G u c = 0
        · have hp2z : p2 G v u d c = 0 :=
            le_antisymm (h0 ▸ p2_le_p1_snd G v u d c) (p2_nonneg G v u d c)
          simp [h0, hp2z]
        · simp [h0, mul_div_cancel₀ _ h0]
    _ = p1 G v d := sum_p2_snd G v u d

lemma stepIn_ent {α : Type*} [Fintype α] {h v u : Fin 10}
    (C : CondPMF G α h) (ev : α → W) (hm : C.HasMarg G ev u) (hadj : D0.Adj v u) :
    (stepIn G C ev hm hadj).ent = C.ent + H2 G v u - H1 G u := by
  unfold CondPMF.ent stepIn
  have hrow : ∀ b : W, p1 G h b * (∑ p : α × W, hEnt (C.q b p.1 * trIn G v u (ev p.1) p.2)) =
      p1 G h b * (∑ x : α, hEnt (C.q b x)) +
      ∑ c : W, p1 G h b * (∑ x : α, if ev x = c then C.q b x else 0) *
        (if p1 G u c = 0 then 0 else ((∑ d : W, hEnt (p2 G v u d c)) - hEnt (p1 G u c)) / p1 G u c) := by
    intro b
    by_cases hb : p1 G h b = 0
    · simp [hb]
    · rw [Fintype.sum_prod_type]
      have hx_eq : ∀ x : α,
          ∑ d : W, hEnt (C.q b x * trIn G v u (ev x) d) =
          hEnt (C.q b x) + C.q b x *
            (if p1 G u (ev x) = 0 then 0
             else ((∑ d : W, hEnt (p2 G v u d (ev x))) - hEnt (p1 G u (ev x))) / p1 G u (ev x)) := by
        intro x
        by_cases hq : C.q b x = 0
        · simp [hq, hEnt_zero]
        · have hpu_ne := C.p1_ne_zero_of_q_ne_zero G hm hb hq
          have hpu_pos : 0 < p1 G u (ev x) := lt_of_le_of_ne (p1_nonneg G u (ev x)) (Ne.symm hpu_ne)
          have h1 : ∀ d : W, hEnt (C.q b x * trIn G v u (ev x) d) =
              C.q b x * hEnt (trIn G v u (ev x) d) + trIn G v u (ev x) d * hEnt (C.q b x) :=
            fun d => hEnt_mul (C.nonneg b x) (trIn_nonneg G v u (ev x) d)
          simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
            sum_trIn_eq_one_of_ne_zero G v u hpu_ne, one_mul, hpu_ne, ↓reduceIte]
          have h2 : ∀ d : W, hEnt (trIn G v u (ev x) d) =
              (hEnt (p2 G v u d (ev x)) - (p2 G v u d (ev x) / p1 G u (ev x)) * hEnt (p1 G u (ev x))) /
              p1 G u (ev x) := by
            intro d
            dsimp [trIn]
            simp only [hpu_ne, ↓reduceIte]
            have hmdiv := mul_hEnt_div (p2_nonneg G v u d (ev x)) hpu_pos
            exact (eq_div_iff hpu_ne).mpr (by linarith)
          have hsum_d : ∑ d : W, hEnt (trIn G v u (ev x) d) =
              ((∑ d : W, hEnt (p2 G v u d (ev x))) - hEnt (p1 G u (ev x))) / p1 G u (ev x) := by
            rw [Finset.sum_congr rfl fun d _ => h2 d, ← Finset.sum_div, Finset.sum_sub_distrib,
              ← Finset.sum_mul, ← Finset.sum_div, sum_p2_fst, div_self hpu_ne, one_mul]
          rw [hsum_d]
          ring
      simp only [hx_eq, Finset.sum_add_distrib, mul_add]
      congr 1
      let g : W → ℝ := fun c =>
        if p1 G u c = 0 then 0 else ((∑ d : W, hEnt (p2 G v u d c)) - hEnt (p1 G u c)) / p1 G u c
      change p1 G h b * ∑ x : α, C.q b x * g (ev x) =
        ∑ c : W, p1 G h b * (∑ x : α, if ev x = c then C.q b x else 0) * g c
      rw [Finset.mul_sum]
      symm
      calc ∑ c : W, p1 G h b * (∑ x : α, if ev x = c then C.q b x else 0) * g c
          = ∑ c : W, ∑ x : α, (if ev x = c then p1 G h b * (C.q b x * g c) else 0) :=
            Finset.sum_congr rfl fun c _ => by
              rw [Finset.mul_sum, Finset.sum_mul]
              exact Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
        _ = ∑ x : α, ∑ c : W, (if ev x = c then p1 G h b * (C.q b x * g c) else 0) :=
            Finset.sum_comm
        _ = ∑ x : α, p1 G h b * (C.q b x * g (ev x)) :=
            Finset.sum_congr rfl fun x _ => by simp
  simp only [hrow, Finset.sum_add_distrib]
  have hH2 : H2 G v u = ∑ c : W, ∑ d : W, hEnt (p2 G v u d c) := by
    unfold H2
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have htele : ∑ b : W, ∑ c : W, p1 G h b * (∑ x : α, if ev x = c then C.q b x else 0) *
      (if p1 G u c = 0 then 0 else ((∑ d : W, hEnt (p2 G v u d c)) - hEnt (p1 G u c)) / p1 G u c) =
      H2 G v u - H1 G u := by
    rw [Finset.sum_comm]
    calc ∑ c : W, ∑ b : W, p1 G h b * (∑ x : α, if ev x = c then C.q b x else 0) *
            (if p1 G u c = 0 then 0
             else ((∑ d : W, hEnt (p2 G v u d c)) - hEnt (p1 G u c)) / p1 G u c)
        = ∑ c : W, p1 G u c *
            (if p1 G u c = 0 then 0
             else ((∑ d : W, hEnt (p2 G v u d c)) - hEnt (p1 G u c)) / p1 G u c) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [← Finset.sum_mul, hm c]
      _ = ∑ c : W, ((∑ d : W, hEnt (p2 G v u d c)) - hEnt (p1 G u c)) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          by_cases h0 : p1 G u c = 0
          · have hd0 : ∀ d : W, hEnt (p2 G v u d c) = 0 := fun d => by
              have : p2 G v u d c = 0 :=
                le_antisymm (h0 ▸ p2_le_p1_snd G v u d c) (p2_nonneg G v u d c)
              rw [this, hEnt_zero]
            simp [h0, hd0, hEnt_zero]
          · simp [h0, mul_div_cancel₀ _ h0]
      _ = H2 G v u - H1 G u := by
          rw [Finset.sum_sub_distrib, hH2]
          rfl
  rw [htele]
  ring

/- #### Unattached and attached-pair Gibbs bounds -/

lemma uncond_ent_le {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    {h : Fin 10} (hM : 0 < (d0Homs G).card)
    (C : CondPMF G α h) (T : Finset β) (emb : α → β)
    (hinj : ∀ b₁ b₂ : W, ∀ x₁ ∈ C.supp b₁, ∀ x₂ ∈ C.supp b₂, emb x₁ = emb x₂ → b₁ = b₂ ∧ x₁ = x₂)
    (hmem : ∀ b : W, ∀ x ∈ C.supp b, emb x ∈ T) :
    0 < T.card ∧ H1 G h + C.ent ≤ Real.log (T.card : ℝ) := by
  let Su : Finset (W × α) := Finset.univ.biUnion (fun b : W => (C.supp b).image (fun x => (b, x)))
  let qu : W × α → ℝ := fun p => p1 G h p.1 * C.q p.1 p.2
  have hqu_nn : ∀ p, 0 ≤ qu p := fun p => mul_nonneg (p1_nonneg G h p.1) (C.nonneg p.1 p.2)
  have hqu_supp : ∀ p, p ∉ Su → qu p = 0 := by
    intro ⟨b, x⟩ hp
    have hx : x ∉ C.supp b := by
      intro hmem_x
      apply hp
      simp only [Su, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨b, x, hmem_x, rfl⟩
    dsimp [qu]
    rw [C.zero_of_not_mem b x hx, mul_zero]
  have hqu_sum : ∑ p : W × α, qu p = 1 := by
    dsimp [qu]
    rw [Fintype.sum_prod_type]
    have hrow : ∀ b : W, ∑ x : α, p1 G h b * C.q b x = p1 G h b := fun b => by
      by_cases hb : p1 G h b = 0
      · simp [hb]
      · rw [← Finset.mul_sum, C.sum_eq b hb, mul_one]
    simp only [hrow]
    exact sum_p1 G hM h
  obtain ⟨hSu_pos, hgibbs⟩ := gibbs_ineq Su qu hqu_nn hqu_supp hqu_sum
  have hent_eq : ∑ p : W × α, hEnt (qu p) = H1 G h + C.ent := by
    dsimp [qu]
    rw [Fintype.sum_prod_type]
    have hrow : ∀ b : W, ∑ x : α, hEnt (p1 G h b * C.q b x) =
        hEnt (p1 G h b) + p1 G h b * ∑ x : α, hEnt (C.q b x) := fun b => by
      by_cases hb : p1 G h b = 0
      · simp [hb, hEnt_zero]
      · have h1 : ∀ x : α, hEnt (p1 G h b * C.q b x) =
            p1 G h b * hEnt (C.q b x) + C.q b x * hEnt (p1 G h b) :=
          fun x => hEnt_mul (p1_nonneg G h b) (C.nonneg b x)
        simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
          C.sum_eq b hb, one_mul]
        ring
    simp only [hrow, Finset.sum_add_distrib]
    rfl
  have hcard_le : Su.card ≤ T.card := by
    have hinj_on : Set.InjOn (fun p : W × α => emb p.2) Su := by
      intro ⟨b1, x1⟩ hp1 ⟨b2, x2⟩ hp2 heq
      simp only [Su, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image, Prod.mk.injEq] at hp1 hp2
      obtain ⟨c1, y1, hy1, rfl, rfl⟩ := hp1
      obtain ⟨c2, y2, hy2, rfl, rfl⟩ := hp2
      obtain ⟨rfl, rfl⟩ := hinj c1 c2 y1 hy1 y2 hy2 heq
      rfl
    have hsub : Su.image (fun p : W × α => emb p.2) ⊆ T := by
      intro z hz
      simp only [Su, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and] at hz
      obtain ⟨⟨b, x⟩, ⟨c, y, hy, heq⟩, rfl⟩ := hz
      cases heq
      exact hmem b x hy
    calc Su.card = (Su.image (fun p : W × α => emb p.2)).card :=
          (Finset.card_image_of_injOn hinj_on).symm
      _ ≤ T.card := Finset.card_le_card hsub
  have hT_pos : 0 < T.card := lt_of_lt_of_le hSu_pos hcard_le
  refine ⟨hT_pos, ?_⟩
  rw [← hent_eq]
  exact le_trans hgibbs (Real.log_le_log (Nat.cast_pos.mpr hSu_pos) (Nat.cast_le.mpr hcard_le))

lemma attached_pair_ent_le {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂]
    [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β]
    {h : Fin 10} (hG : G.IsTournament) (hM : 0 < (d0Homs G).card)
    (C_out : CondPMF G α₁ h) (C_in : CondPMF G α₂ h)
    (T : Finset β) (emb₁ : α₁ → β) (emb₂ : α₂ → β) (rt : β → W)
    (hinj₁ : ∀ b : W, Set.InjOn emb₁ (C_out.supp b))
    (hmem₁ : ∀ b : W, ∀ x ∈ C_out.supp b, emb₁ x ∈ T ∧ G.Adj b (rt (emb₁ x)))
    (hinj₂ : ∀ b : W, Set.InjOn emb₂ (C_in.supp b))
    (hmem₂ : ∀ b : W, ∀ y ∈ C_in.supp b, emb₂ y ∈ T ∧ G.Adj (rt (emb₂ y)) b) :
    0 < T.card ∧ C_out.ent + C_in.ent ≤ 2 * Real.log (T.card : ℝ) - 2 * Real.log 2 := by
  have hcard_sum : ∀ b : W, (C_out.supp b).card + (C_in.supp b).card ≤ T.card := by
    intro b
    let S1 := (C_out.supp b).image emb₁
    let S2 := (C_in.supp b).image emb₂
    have hdisj : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      rw [Finset.mem_image] at hz1 hz2
      obtain ⟨x, hx, rfl⟩ := hz1
      obtain ⟨y, hy, heq⟩ := hz2
      have hadj1 := (hmem₁ b x hx).2
      have hadj2 := heq ▸ (hmem₂ b y hy).2
      exact tournament_asym G hG hadj1 hadj2
    have hsub : S1 ∪ S2 ⊆ T := by
      intro z hz
      rw [Finset.mem_union] at hz
      rcases hz with hz1 | hz2
      · rw [Finset.mem_image] at hz1; obtain ⟨x, hx, rfl⟩ := hz1; exact (hmem₁ b x hx).1
      · rw [Finset.mem_image] at hz2; obtain ⟨y, hy, rfl⟩ := hz2; exact (hmem₂ b y hy).1
    have := Finset.card_le_card hsub
    rwa [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn (hinj₁ b),
      Finset.card_image_of_injOn (hinj₂ b)] at this
  obtain ⟨f0, hf0⟩ := Finset.card_pos.mp hM
  have hp0 : p1 G h (f0 h) ≠ 0 := (p1_pos_of_mem_d0Homs G hf0 h).ne'
  obtain ⟨hc1_pos, _⟩ := gibbs_ineq (C_out.supp (f0 h)) (C_out.q (f0 h))
    (C_out.nonneg (f0 h)) (C_out.zero_of_not_mem (f0 h)) (C_out.sum_eq (f0 h) hp0)
  have hT_pos : 0 < T.card := lt_of_lt_of_le hc1_pos
    (le_trans (Nat.le_add_right _ _) (hcard_sum (f0 h)))
  refine ⟨hT_pos, ?_⟩
  have hb_bound : ∀ b : W,
      p1 G h b * ((∑ x : α₁, hEnt (C_out.q b x)) + (∑ y : α₂, hEnt (C_in.q b y))) ≤
      p1 G h b * (2 * Real.log (T.card : ℝ) - 2 * Real.log 2) := by
    intro b
    by_cases hb : p1 G h b = 0
    · simp [hb]
    · obtain ⟨ho_pos, ho_le⟩ := gibbs_ineq (C_out.supp b) (C_out.q b)
        (C_out.nonneg b) (C_out.zero_of_not_mem b) (C_out.sum_eq b hb)
      obtain ⟨hi_pos, hi_le⟩ := gibbs_ineq (C_in.supp b) (C_in.q b)
        (C_in.nonneg b) (C_in.zero_of_not_mem b) (C_in.sum_eq b hb)
      refine mul_le_mul_of_nonneg_left ?_ (p1_nonneg G h b)
      have hprod_le : (4 : ℝ) * (((C_out.supp b).card : ℝ) * ((C_in.supp b).card : ℝ)) ≤
          (T.card : ℝ) ^ 2 := by
        exact_mod_cast le_trans (four_mul_le_add_sq _ _) (Nat.pow_le_pow_left (hcard_sum b) 2)
      have ho_r : (0 : ℝ) < ((C_out.supp b).card : ℝ) := Nat.cast_pos.mpr ho_pos
      have hi_r : (0 : ℝ) < ((C_in.supp b).card : ℝ) := Nat.cast_pos.mpr hi_pos
      have hlog_prod := Real.log_le_log (by positivity) hprod_le
      rw [Real.log_mul (by norm_num) (mul_pos ho_r hi_r).ne',
        Real.log_mul ho_r.ne' hi_r.ne', Real.log_pow,
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hlog_prod
      push_cast at hlog_prod
      linarith [ho_le, hi_le, hlog_prod]
  have hsum_le := Finset.sum_le_sum (s := (Finset.univ : Finset W)) fun b _ => hb_bound b
  have hlhs : ∑ b : W, p1 G h b *
      ((∑ x : α₁, hEnt (C_out.q b x)) + (∑ y : α₂, hEnt (C_in.q b y))) =
      C_out.ent + C_in.ent := by
    simp only [mul_add, Finset.sum_add_distrib]
    rfl
  have hrhs : ∑ b : W, p1 G h b * (2 * Real.log (T.card : ℝ) - 2 * Real.log 2) =
      2 * Real.log (T.card : ℝ) - 2 * Real.log 2 := by
    rw [← Finset.sum_mul, sum_p1 G hM h, one_mul]
  linarith [hsum_le, hlhs, hrhs]

end EntropyEngine

/- ### Section 4: The 11 sandwich component inequalities and main D0 bound -/

private lemma log_le_of_mul_le_pow {n k c d : ℕ} (hk : 0 < k) (hn : 0 < n)
    (h : 2 ^ c * k ≤ n ^ d) :
    Real.log (k : ℝ) ≤ (d : ℝ) * Real.log (n : ℝ) - (c : ℝ) * Real.log 2 := by
  have hk_r : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_r : (2 : ℝ) ^ c * (k : ℝ) ≤ (n : ℝ) ^ d := by exact_mod_cast h
  have hlog := Real.log_le_log (by positivity) h_r
  rw [Real.log_mul (by positivity) hk_r.ne', Real.log_pow, Real.log_pow] at hlog
  linarith

section SandwichAssembly

variable {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
  (G : Digraph W) [DecidableRel G.Adj]

lemma homCount_D0_bound (hG : G.IsTournament) :
    Digraph.homDensity D0 G ≤ (1 / 2 : ℝ) ^ 9 := by
  have hn_pos : 0 < Fintype.card W := Fintype.card_pos
  have hn_r : (0 : ℝ) < (Fintype.card W : ℝ) := Nat.cast_pos.mpr hn_pos
  unfold Digraph.homDensity
  rw [Fintype.card_fin, homCount_D0_eq]
  by_cases hM0 : (d0Homs G).card = 0
  · rw [hM0]; simp only [Nat.cast_zero, zero_div]; positivity
  have hM : 0 < (d0Homs G).card := Nat.pos_of_ne_zero hM0
  have hM_r : (0 : ℝ) < ((d0Homs G).card : ℝ) := Nat.cast_pos.mpr hM
  -- Adjacency witnesses on D0
  have hadj01 : D0.Adj 0 1 := by decide
  have hadj12 : D0.Adj 1 2 := by decide
  have hadj23 : D0.Adj 2 3 := by decide
  have hadj43 : D0.Adj 4 3 := by decide
  have hadj54 : D0.Adj 5 4 := by decide
  have hadj65 : D0.Adj 6 5 := by decide
  have hadj76 : D0.Adj 7 6 := by decide
  have hadj48 : D0.Adj 4 8 := by decide
  have hadj89 : D0.Adj 8 9 := by decide
  set logN : ℝ := Real.log (Fintype.card W : ℝ)
  set log2 : ℝ := Real.log 2

  -- Component 1: r01 (mult 8), unattached arc 0->1
  have h_r01 : H2 G 0 1 ≤ 2 * logN - log2 := by
    let s0 := condBase G 0
    let s1 := stepOut G s0 id (condBase_hasMarg G 0) hadj01
    obtain ⟨hc_pos, hle⟩ := uncond_ent_le G hM s1 (arcsFinset G) id
      (fun b1 b2 x1 hx1 x2 hx2 heq => by
        simp only [s1, s0, stepOut, condBase, Finset.mem_filter, Finset.mem_product,
          Finset.mem_singleton, Finset.mem_univ, and_true] at hx1 hx2
        subst heq; exact ⟨hx1.1.symm.trans hx2.1, rfl⟩)
      (fun b x hx => by
        simp only [s1, s0, stepOut, condBase, arcsFinset, Finset.mem_filter,
          Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true, true_and] at hx ⊢
        exact hx.2)
    have hent : H1 G 0 + s1.ent = H2 G 0 1 := by
      dsimp [s1, s0]
      rw [stepOut_ent, condBase_ent]; ring
    have hcard := log_le_of_mul_le_pow (c := 1) (d := 2) hc_pos hn_pos
      (by simpa using two_mul_card_arcs_le G hG)
    push_cast at hcard
    dsimp [logN, log2] at hcard ⊢
    linarith [hle, hent, hcard]

  -- Component 2: D2star (mult 16), unattached cev(P_{2,2}) on 4->8->9, 4->8->9
  have h_d2 : 2 * H2 G 4 8 + 2 * H2 G 8 9 - H1 G 4 - 2 * H1 G 8 ≤ 5 * logN - 4 * log2 := by
    let s0 := condBase G 4
    have hm0 := condBase_hasMarg G 4
    let s1 := stepOut G s0 id hm0 hadj48
    have hm1_0 := stepOut_hasMarg_fst G s0 id hm0 hadj48 hm0
    have hm1_1 := stepOut_hasMarg_snd G s0 id hm0 hadj48
    let s2 := stepOut G s1 Prod.snd hm1_1 hadj89
    have hm2_0 := stepOut_hasMarg_fst G s1 Prod.snd hm1_1 hadj89 hm1_0
    let s3 := stepOut G s2 (fun p => p.1.1) hm2_0 hadj48
    have hm3_3 := stepOut_hasMarg_snd G s2 (fun p => p.1.1) hm2_0 hadj48
    let s4 := stepOut G s3 Prod.snd hm3_3 hadj89
    let emb : (((W × W) × W) × W) × W → W × (W × W) × (W × W) :=
      fun p => (p.1.1.1.1, (p.1.1.1.2, p.1.1.2), (p.1.2, p.2))
    obtain ⟨hc_pos, hle⟩ := uncond_ent_le G hM s4 (p22RevFinset G) emb
      (fun b1 b2 x1 hx1 x2 hx2 heq => by
        simp only [s4, s3, s2, s1, s0, stepOut, condBase, Finset.mem_filter,
          Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true] at hx1 hx2
        rcases x1 with ⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩
        rcases x2 with ⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := heq
        exact ⟨hx1.1.1.1.1.symm.trans hx2.1.1.1.1, rfl⟩)
      (fun b x hx => by
        simp only [s4, s3, s2, s1, s0, stepOut, condBase, p22RevFinset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨hx.1.1.1.2, hx.1.1.2, hx.1.2, hx.2⟩)
    have hent : H1 G 4 + s4.ent = 2 * H2 G 4 8 + 2 * H2 G 8 9 - H1 G 4 - 2 * H1 G 8 := by
      dsimp [s4, s3, s2, s1, s0]
      rw [stepOut_ent, stepOut_ent, stepOut_ent, stepOut_ent, condBase_ent]; ring
    have hc_r : (0 : ℝ) < ((p22RevFinset G).card : ℝ) := Nat.cast_pos.mpr hc_pos
    have h16 := sixteen_mul_card_p22Rev_le G hG
    have hlog := Real.log_le_log (by positivity) h16
    rw [Real.log_mul (by norm_num) hc_r.ne', Real.log_pow,
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at hlog
    push_cast at hlog
    dsimp [logN, log2]
    linarith [hle, hent, hlog]

  -- Component 3: (u0p, u2m) (mult 10), P_0 attached at vertex 1
  have h_u0 : H2 G 0 1 + H2 G 1 2 - 2 * H1 G 1 ≤ 2 * logN - 2 * log2 := by
    let c0 := condBase G 1
    have hm0 := condBase_hasMarg G 1
    let c_out := stepOut G c0 id hm0 hadj12
    let c_in := stepIn G c0 id hm0 hadj01
    obtain ⟨_, hle⟩ := attached_pair_ent_le G hG hM c_out c_in
      (Finset.univ : Finset W) Prod.snd Prod.snd id
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_out, c0, stepOut, condBase, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true] at hx1 hx2
        exact Prod.ext (hx1.1.trans hx2.1.symm) heq)
      (fun b x hx => by
        simp only [c_out, c0, stepOut, condBase, Finset.mem_filter, Finset.mem_product,
          Finset.mem_singleton, Finset.mem_univ, and_true] at hx
        exact ⟨Finset.mem_univ _, hx.1 ▸ hx.2⟩)
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_in, c0, stepIn, condBase, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true] at hx1 hx2
        exact Prod.ext (hx1.1.trans hx2.1.symm) heq)
      (fun b x hx => by
        simp only [c_in, c0, stepIn, condBase, Finset.mem_filter, Finset.mem_product,
          Finset.mem_singleton, Finset.mem_univ, and_true] at hx
        exact ⟨Finset.mem_univ _, hx.1 ▸ hx.2⟩)
    have hent : c_out.ent + c_in.ent = H2 G 0 1 + H2 G 1 2 - 2 * H1 G 1 := by
      dsimp [c_out, c_in, c0]
      rw [stepOut_ent, stepIn_ent, condBase_ent]; ring
    rw [Finset.card_univ] at hle
    dsimp [logN, log2]
    linarith [hle, hent]

  -- Component 4: (u01_1p, u23_3m) (mult 10), P_1 rooted at head attached at vertex 2
  have h_u1 : H2 G 0 1 + H2 G 1 2 + 2 * H2 G 2 3 - H1 G 1 - 2 * H1 G 2 - H1 G 3 ≤
      4 * logN - 4 * log2 := by
    let c0 := condBase G 2
    have hm0 := condBase_hasMarg G 2
    let co1 := stepOut G c0 id hm0 hadj23
    let c_out := stepIn G co1 Prod.snd (stepOut_hasMarg_snd G c0 id hm0 hadj23) hadj23
    let ci1 := stepIn G c0 id hm0 hadj12
    let c_in := stepIn G ci1 Prod.snd (stepIn_hasMarg_snd G c0 id hm0 hadj12) hadj01
    let emb : (W × W) × W → W × W := fun p => (p.2, p.1.2)
    obtain ⟨hc_pos, hle⟩ := attached_pair_ent_le G hG hM c_out c_in
      (arcsFinset G) emb emb Prod.snd
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_out, co1, c0, stepIn, stepOut, condBase, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true] at hx1 hx2
        rcases x1 with ⟨⟨b1, r1⟩, l1⟩; rcases x2 with ⟨⟨b2, r2⟩, l2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact Prod.ext (Prod.ext (hx1.1.1.trans hx2.1.1.symm) rfl) rfl)
      (fun b x hx => by
        simp only [c_out, co1, c0, stepIn, stepOut, condBase, arcsFinset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨hx.2, hx.1.1 ▸ hx.1.2⟩)
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_in, ci1, c0, stepIn, condBase, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true] at hx1 hx2
        rcases x1 with ⟨⟨b1, r1⟩, l1⟩; rcases x2 with ⟨⟨b2, r2⟩, l2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact Prod.ext (Prod.ext (hx1.1.1.trans hx2.1.1.symm) rfl) rfl)
      (fun b x hx => by
        simp only [c_in, ci1, c0, stepIn, condBase, arcsFinset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨hx.2, hx.1.1 ▸ hx.1.2⟩)
    have hent : c_out.ent + c_in.ent =
        H2 G 0 1 + H2 G 1 2 + 2 * H2 G 2 3 - H1 G 1 - 2 * H1 G 2 - H1 G 3 := by
      dsimp [c_out, co1, c_in, ci1, c0]
      rw [stepIn_ent, stepOut_ent, stepIn_ent, stepIn_ent, condBase_ent]; ring
    have hcard := log_le_of_mul_le_pow (c := 1) (d := 2) hc_pos hn_pos
      (by simpa using two_mul_card_arcs_le G hG)
    push_cast at hcard
    dsimp [logN, log2] at hcard ⊢
    linarith [hle, hent, hcard]

  -- Component 5: (u_in4, u_out4) (mult 5), P_2 rooted at head attached at vertex 4
  have h_u4 : 2 * H2 G 4 3 + 2 * H2 G 5 4 + H2 G 6 5 + H2 G 7 6 -
      H1 G 3 - 3 * H1 G 4 - H1 G 5 - H1 G 6 ≤ 6 * logN - 6 * log2 := by
    let c0 := condBase G 4
    have hm0 := condBase_hasMarg G 4
    let co1 := stepOut G c0 id hm0 hadj43
    let co2 := stepIn G co1 Prod.snd (stepOut_hasMarg_snd G c0 id hm0 hadj43) hadj43
    let c_out := stepIn G co2 Prod.snd
      (stepIn_hasMarg_snd G co1 Prod.snd (stepOut_hasMarg_snd G c0 id hm0 hadj43) hadj43) hadj54
    let ci1 := stepIn G c0 id hm0 hadj54
    let ci2 := stepIn G ci1 Prod.snd (stepIn_hasMarg_snd G c0 id hm0 hadj54) hadj65
    let c_in := stepIn G ci2 Prod.snd
      (stepIn_hasMarg_snd G ci1 Prod.snd (stepIn_hasMarg_snd G c0 id hm0 hadj54) hadj65) hadj76
    let emb : ((W × W) × W) × W → W × W × W := fun p => (p.2, p.1.2, p.1.1.2)
    obtain ⟨hc_pos, hle⟩ := attached_pair_ent_le G hG hM c_out c_in
      (p2Finset G) emb emb (fun t => t.2.2)
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_out, co2, co1, c0, stepIn, stepOut, condBase, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true] at hx1 hx2
        rcases x1 with ⟨⟨⟨b1, r1⟩, m1⟩, l1⟩; rcases x2 with ⟨⟨⟨b2, r2⟩, m2⟩, l2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact Prod.ext (Prod.ext (Prod.ext (hx1.1.1.1.trans hx2.1.1.1.symm) rfl) rfl) rfl)
      (fun b x hx => by
        simp only [c_out, co2, co1, c0, stepIn, stepOut, condBase, p2Finset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨⟨hx.2, hx.1.2⟩, hx.1.1.1 ▸ hx.1.1.2⟩)
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_in, ci2, ci1, c0, stepIn, condBase, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true] at hx1 hx2
        rcases x1 with ⟨⟨⟨b1, r1⟩, m1⟩, l1⟩; rcases x2 with ⟨⟨⟨b2, r2⟩, m2⟩, l2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact Prod.ext (Prod.ext (Prod.ext (hx1.1.1.1.trans hx2.1.1.1.symm) rfl) rfl) rfl)
      (fun b x hx => by
        simp only [c_in, ci2, ci1, c0, stepIn, condBase, p2Finset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨⟨hx.2, hx.1.2⟩, hx.1.1.1 ▸ hx.1.1.2⟩)
    have hent : c_out.ent + c_in.ent =
        2 * H2 G 4 3 + 2 * H2 G 5 4 + H2 G 6 5 + H2 G 7 6 -
        H1 G 3 - 3 * H1 G 4 - H1 G 5 - H1 G 6 := by
      dsimp [c_out, co2, co1, c_in, ci2, ci1, c0]
      rw [stepIn_ent, stepIn_ent, stepOut_ent, stepIn_ent, stepIn_ent, stepIn_ent, condBase_ent]
      ring
    have hcard := log_le_of_mul_le_pow (c := 2) (d := 3) hc_pos hn_pos
      (by simpa using four_mul_card_p2_le G hG)
    dsimp [logN, log2] at hcard ⊢
    linarith [hle, hent, hcard]

  -- Component 6: (y_in4, y_out4) (mult 8), P_2 rooted at head attached at vertex 4
  have h_y4 : H2 G 1 2 + H2 G 2 3 + H2 G 4 3 + H2 G 5 4 + H2 G 6 5 + H2 G 7 6 -
      H1 G 2 - H1 G 3 - 2 * H1 G 4 - H1 G 5 - H1 G 6 ≤ 6 * logN - 6 * log2 := by
    let c0 := condBase G 4
    have hm0 := condBase_hasMarg G 4
    let co1 := stepOut G c0 id hm0 hadj43
    let co2 := stepIn G co1 Prod.snd (stepOut_hasMarg_snd G c0 id hm0 hadj43) hadj23
    let c_out := stepIn G co2 Prod.snd
      (stepIn_hasMarg_snd G co1 Prod.snd (stepOut_hasMarg_snd G c0 id hm0 hadj43) hadj23) hadj12
    let ci1 := stepIn G c0 id hm0 hadj54
    let ci2 := stepIn G ci1 Prod.snd (stepIn_hasMarg_snd G c0 id hm0 hadj54) hadj65
    let c_in := stepIn G ci2 Prod.snd
      (stepIn_hasMarg_snd G ci1 Prod.snd (stepIn_hasMarg_snd G c0 id hm0 hadj54) hadj65) hadj76
    let emb : ((W × W) × W) × W → W × W × W := fun p => (p.2, p.1.2, p.1.1.2)
    obtain ⟨hc_pos, hle⟩ := attached_pair_ent_le G hG hM c_out c_in
      (p2Finset G) emb emb (fun t => t.2.2)
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_out, co2, co1, c0, stepIn, stepOut, condBase, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true] at hx1 hx2
        rcases x1 with ⟨⟨⟨b1, r1⟩, m1⟩, l1⟩; rcases x2 with ⟨⟨⟨b2, r2⟩, m2⟩, l2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact Prod.ext (Prod.ext (Prod.ext (hx1.1.1.1.trans hx2.1.1.1.symm) rfl) rfl) rfl)
      (fun b x hx => by
        simp only [c_out, co2, co1, c0, stepIn, stepOut, condBase, p2Finset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨⟨hx.2, hx.1.2⟩, hx.1.1.1 ▸ hx.1.1.2⟩)
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_in, ci2, ci1, c0, stepIn, condBase, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true] at hx1 hx2
        rcases x1 with ⟨⟨⟨b1, r1⟩, m1⟩, l1⟩; rcases x2 with ⟨⟨⟨b2, r2⟩, m2⟩, l2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact Prod.ext (Prod.ext (Prod.ext (hx1.1.1.1.trans hx2.1.1.1.symm) rfl) rfl) rfl)
      (fun b x hx => by
        simp only [c_in, ci2, ci1, c0, stepIn, condBase, p2Finset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨⟨hx.2, hx.1.2⟩, hx.1.1.1 ▸ hx.1.1.2⟩)
    have hent : c_out.ent + c_in.ent =
        H2 G 1 2 + H2 G 2 3 + H2 G 4 3 + H2 G 5 4 + H2 G 6 5 + H2 G 7 6 -
        H1 G 2 - H1 G 3 - 2 * H1 G 4 - H1 G 5 - H1 G 6 := by
      dsimp [c_out, co2, co1, c_in, ci2, ci1, c0]
      rw [stepIn_ent, stepIn_ent, stepOut_ent, stepIn_ent, stepIn_ent, stepIn_ent, condBase_ent]
      ring
    have hcard := log_le_of_mul_le_pow (c := 2) (d := 3) hc_pos hn_pos
      (by simpa using four_mul_card_p2_le G hG)
    dsimp [logN, log2] at hcard ⊢
    linarith [hle, hent, hcard]

  -- Component 7: (z_out4, z_in4) (mult 4), P_{1,2} rooted at sink attached at vertex 4
  have h_z4 : H2 G 1 2 + H2 G 2 3 + 2 * H2 G 4 3 + H2 G 5 4 + 2 * H2 G 6 5 + H2 G 7 6 -
      H1 G 2 - 2 * H1 G 3 - 2 * H1 G 4 - 2 * H1 G 5 - H1 G 6 ≤ 8 * logN - 8 * log2 := by
    let c0 := condBase G 4
    have hm0 := condBase_hasMarg G 4
    let co1 := stepOut G c0 id hm0 hadj43
    have hmo1 := stepOut_hasMarg_snd G c0 id hm0 hadj43
    let co2 := stepIn G co1 Prod.snd hmo1 hadj43
    have hmo2_r := stepIn_hasMarg_fst G co1 Prod.snd hmo1 hadj43 hmo1
    let co3 := stepIn G co2 (fun p => p.1.2) hmo2_r hadj23
    let c_out := stepIn G co3 Prod.snd
      (stepIn_hasMarg_snd G co2 (fun p => p.1.2) hmo2_r hadj23) hadj12
    let ci1 := stepIn G c0 id hm0 hadj54
    have hmi1 := stepIn_hasMarg_snd G c0 id hm0 hadj54
    let ci2 := stepIn G ci1 Prod.snd hmi1 hadj65
    have hmi2_r := stepIn_hasMarg_fst G ci1 Prod.snd hmi1 hadj65 hmi1
    let ci3 := stepIn G ci2 (fun p => p.1.2) hmi2_r hadj65
    let c_in := stepIn G ci3 Prod.snd
      (stepIn_hasMarg_snd G ci2 (fun p => p.1.2) hmi2_r hadj65) hadj76
    let emb : (((W × W) × W) × W) × W → (W × W) × (W × W) :=
      fun p => ((p.1.1.2, p.1.1.1.2), (p.1.2, p.2))
    obtain ⟨hc_pos, hle⟩ := attached_pair_ent_le G hG hM c_out c_in
      (p12Finset G) emb emb (fun q => q.1.2)
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_out, co3, co2, co1, c0, stepIn, stepOut, condBase, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true] at hx1 hx2
        rcases x1 with ⟨⟨⟨⟨b1, r1⟩, a1⟩, m1⟩, d1⟩
        rcases x2 with ⟨⟨⟨⟨b2, r2⟩, a2⟩, m2⟩, d2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := heq
        exact Prod.ext (Prod.ext (Prod.ext (Prod.ext (hx1.1.1.1.1.trans hx2.1.1.1.1.symm) rfl)
          rfl) rfl) rfl)
      (fun b x hx => by
        simp only [c_out, co3, co2, co1, c0, stepIn, stepOut, condBase, p12Finset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨⟨hx.1.1.2, hx.1.2, hx.2⟩, hx.1.1.1.1 ▸ hx.1.1.1.2⟩)
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_in, ci3, ci2, ci1, c0, stepIn, condBase, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true] at hx1 hx2
        rcases x1 with ⟨⟨⟨⟨b1, r1⟩, a1⟩, m1⟩, d1⟩
        rcases x2 with ⟨⟨⟨⟨b2, r2⟩, a2⟩, m2⟩, d2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := heq
        exact Prod.ext (Prod.ext (Prod.ext (Prod.ext (hx1.1.1.1.1.trans hx2.1.1.1.1.symm) rfl)
          rfl) rfl) rfl)
      (fun b x hx => by
        simp only [c_in, ci3, ci2, ci1, c0, stepIn, condBase, p12Finset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨⟨hx.1.1.2, hx.1.2, hx.2⟩, hx.1.1.1.1 ▸ hx.1.1.1.2⟩)
    have hent : c_out.ent + c_in.ent =
        H2 G 1 2 + H2 G 2 3 + 2 * H2 G 4 3 + H2 G 5 4 + 2 * H2 G 6 5 + H2 G 7 6 -
        H1 G 2 - 2 * H1 G 3 - 2 * H1 G 4 - 2 * H1 G 5 - H1 G 6 := by
      dsimp [c_out, co3, co2, co1, c_in, ci3, ci2, ci1, c0]
      rw [stepIn_ent, stepIn_ent, stepIn_ent, stepOut_ent,
          stepIn_ent, stepIn_ent, stepIn_ent, stepIn_ent, condBase_ent]
      ring
    have hcard := log_le_of_mul_le_pow (c := 3) (d := 4) hc_pos hn_pos
      (by simpa using eight_mul_card_p12_le G hG)
    dsimp [logN, log2] at hcard ⊢
    linarith [hle, hent, hcard]

  -- Unattached helper: P_{1,1}^in on 0->1 and 7->6
  have h_p11_01 : 0 < (p11InFinset G).card ∧
      2 * H2 G 0 1 - H1 G 1 ≤ Real.log ((p11InFinset G).card : ℝ) := by
    let s0 := condBase G 1
    have hm0 := condBase_hasMarg G 1
    let s1 := stepIn G s0 id hm0 hadj01
    let s2 := stepIn G s1 Prod.fst (stepIn_hasMarg_fst G s0 id hm0 hadj01 hm0) hadj01
    let emb : (W × W) × W → W × W × W := fun p => (p.1.1, p.1.2, p.2)
    obtain ⟨hc_pos, hle⟩ := uncond_ent_le G hM s2 (p11InFinset G) emb
      (fun b1 b2 x1 hx1 x2 hx2 heq => by
        simp only [s2, s1, s0, stepIn, condBase, Finset.mem_filter, Finset.mem_product,
          Finset.mem_singleton, Finset.mem_univ, and_true] at hx1 hx2
        rcases x1 with ⟨⟨a1, y1⟩, z1⟩; rcases x2 with ⟨⟨a2, y2⟩, z2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact ⟨hx1.1.1.symm.trans hx2.1.1, rfl⟩)
      (fun b x hx => by
        simp only [s2, s1, s0, stepIn, condBase, p11InFinset, emb, Finset.mem_filter,
          Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true, true_and] at hx ⊢
        exact ⟨hx.1.2, hx.2⟩)
    have hent : H1 G 1 + s2.ent = 2 * H2 G 0 1 - H1 G 1 := by
      dsimp [s2, s1, s0]
      rw [stepIn_ent, stepIn_ent, condBase_ent]; ring
    exact ⟨hc_pos, by linarith [hle, hent]⟩

  have h_p11_76 : 2 * H2 G 7 6 - H1 G 6 ≤ Real.log ((p11InFinset G).card : ℝ) := by
    let s0 := condBase G 6
    have hm0 := condBase_hasMarg G 6
    let s1 := stepIn G s0 id hm0 hadj76
    let s2 := stepIn G s1 Prod.fst (stepIn_hasMarg_fst G s0 id hm0 hadj76 hm0) hadj76
    let emb : (W × W) × W → W × W × W := fun p => (p.1.1, p.1.2, p.2)
    obtain ⟨_, hle⟩ := uncond_ent_le G hM s2 (p11InFinset G) emb
      (fun b1 b2 x1 hx1 x2 hx2 heq => by
        simp only [s2, s1, s0, stepIn, condBase, Finset.mem_filter, Finset.mem_product,
          Finset.mem_singleton, Finset.mem_univ, and_true] at hx1 hx2
        rcases x1 with ⟨⟨a1, y1⟩, z1⟩; rcases x2 with ⟨⟨a2, y2⟩, z2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact ⟨hx1.1.1.symm.trans hx2.1.1, rfl⟩)
      (fun b x hx => by
        simp only [s2, s1, s0, stepIn, condBase, p11InFinset, emb, Finset.mem_filter,
          Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true, true_and] at hx ⊢
        exact ⟨hx.1.2, hx.2⟩)
    have hent : H1 G 6 + s2.ent = 2 * H2 G 7 6 - H1 G 6 := by
      dsimp [s2, s1, s0]
      rw [stepIn_ent, stepIn_ent, condBase_ent]; ring
    linarith [hle, hent]

  -- Component 8: w group (mult 2), P_2 rooted at middle at vertex 5 + w_01 + w_76
  have h_w : 2 * H2 G 0 1 + H2 G 4 3 + 2 * H2 G 5 4 + 2 * H2 G 6 5 + 3 * H2 G 7 6 -
      H1 G 1 - 2 * H1 G 4 - 2 * H1 G 5 - 3 * H1 G 6 ≤ 12 * logN - 10 * log2 := by
    let c0 := condBase G 5
    have hm0 := condBase_hasMarg G 5
    let co1 := stepOut G c0 id hm0 hadj54
    have hmo1 := stepOut_hasMarg_snd G c0 id hm0 hadj54
    let co2 := stepIn G co1 Prod.snd hmo1 hadj54
    let c_out := stepOut G co2 (fun p => p.1.2)
      (stepIn_hasMarg_fst G co1 Prod.snd hmo1 hadj54 hmo1) hadj43
    let ci1 := stepIn G c0 id hm0 hadj65
    have hmi1 := stepIn_hasMarg_snd G c0 id hm0 hadj65
    let ci2 := stepIn G ci1 Prod.snd hmi1 hadj76
    let c_in := stepOut G ci2 (fun p => p.1.2)
      (stepIn_hasMarg_fst G ci1 Prod.snd hmi1 hadj76 hmi1) hadj65
    let emb : ((W × W) × W) × W → W × W × W := fun p => (p.1.2, p.1.1.2, p.2)
    obtain ⟨hp2_pos, hle⟩ := attached_pair_ent_le G hG hM c_out c_in
      (p2Finset G) emb emb (fun t => t.2.1)
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_out, co2, co1, c0, stepOut, stepIn, condBase, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true] at hx1 hx2
        rcases x1 with ⟨⟨⟨b1, m1⟩, l1⟩, r1⟩; rcases x2 with ⟨⟨⟨b2, m2⟩, l2⟩, r2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact Prod.ext (Prod.ext (Prod.ext (hx1.1.1.1.trans hx2.1.1.1.symm) rfl) rfl) rfl)
      (fun b x hx => by
        simp only [c_out, co2, co1, c0, stepOut, stepIn, condBase, p2Finset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨⟨hx.1.2, hx.2⟩, hx.1.1.1 ▸ hx.1.1.2⟩)
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_in, ci2, ci1, c0, stepOut, stepIn, condBase, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true] at hx1 hx2
        rcases x1 with ⟨⟨⟨b1, m1⟩, l1⟩, r1⟩; rcases x2 with ⟨⟨⟨b2, m2⟩, l2⟩, r2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact Prod.ext (Prod.ext (Prod.ext (hx1.1.1.1.trans hx2.1.1.1.symm) rfl) rfl) rfl)
      (fun b x hx => by
        simp only [c_in, ci2, ci1, c0, stepOut, stepIn, condBase, p2Finset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨⟨hx.1.2, hx.2⟩, hx.1.1.1 ▸ hx.1.1.2⟩)
    have hent : c_out.ent + c_in.ent =
        H2 G 4 3 + 2 * H2 G 5 4 + 2 * H2 G 6 5 + H2 G 7 6 -
        2 * H1 G 4 - 2 * H1 G 5 - 2 * H1 G 6 := by
      dsimp [c_out, co2, co1, c_in, ci2, ci1, c0]
      rw [stepOut_ent, stepIn_ent, stepOut_ent, stepOut_ent, stepIn_ent, stepIn_ent, condBase_ent]
      ring
    have hprod_pos : 0 < (p2Finset G).card * (p11InFinset G).card :=
      Nat.mul_pos hp2_pos h_p11_01.1
    have hprod_log := log_le_of_mul_le_pow (c := 4) (d := 6) hprod_pos hn_pos
      (by simpa using sixteen_mul_p2_mul_p11In_le G hG)
    have hp2_r : (0 : ℝ) < ((p2Finset G).card : ℝ) := Nat.cast_pos.mpr hp2_pos
    have hp11_r : (0 : ℝ) < ((p11InFinset G).card : ℝ) := Nat.cast_pos.mpr h_p11_01.1
    rw [Nat.cast_mul, Real.log_mul hp2_r.ne' hp11_r.ne'] at hprod_log
    dsimp [logN, log2] at hprod_log ⊢
    linarith [hle, hent, h_p11_01.2, h_p11_76, hprod_log]

  -- Component 9: x/a/b group (mult 1), P_2 rooted at tail at vertex 6 + x_76 + b_76
  have h_xab : H2 G 4 3 + H2 G 5 4 + 2 * H2 G 6 5 + 6 * H2 G 7 6 -
      H1 G 4 - H1 G 5 - 5 * H1 G 6 - H1 G 7 ≤ 12 * logN - 10 * log2 := by
    let c0 := condBase G 6
    have hm0 := condBase_hasMarg G 6
    let co1 := stepOut G c0 id hm0 hadj65
    let co2 := stepOut G co1 Prod.snd (stepOut_hasMarg_snd G c0 id hm0 hadj65) hadj54
    let c_out := stepOut G co2 Prod.snd
      (stepOut_hasMarg_snd G co1 Prod.snd (stepOut_hasMarg_snd G c0 id hm0 hadj65) hadj54) hadj43
    let ci1 := stepIn G c0 id hm0 hadj76
    let ci2 := stepOut G ci1 Prod.snd (stepIn_hasMarg_snd G c0 id hm0 hadj76) hadj76
    let c_in := stepOut G ci2 Prod.snd
      (stepOut_hasMarg_snd G ci1 Prod.snd (stepIn_hasMarg_snd G c0 id hm0 hadj76) hadj76) hadj65
    let emb : ((W × W) × W) × W → W × W × W := fun p => (p.1.1.2, p.1.2, p.2)
    obtain ⟨hp2_pos, hle⟩ := attached_pair_ent_le G hG hM c_out c_in
      (p2Finset G) emb emb (fun t => t.1)
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_out, co2, co1, c0, stepOut, condBase, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true] at hx1 hx2
        rcases x1 with ⟨⟨⟨b1, l1⟩, m1⟩, r1⟩; rcases x2 with ⟨⟨⟨b2, l2⟩, m2⟩, r2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact Prod.ext (Prod.ext (Prod.ext (hx1.1.1.1.trans hx2.1.1.1.symm) rfl) rfl) rfl)
      (fun b x hx => by
        simp only [c_out, co2, co1, c0, stepOut, condBase, p2Finset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨⟨hx.1.2, hx.2⟩, hx.1.1.1 ▸ hx.1.1.2⟩)
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_in, ci2, ci1, c0, stepOut, stepIn, condBase, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true] at hx1 hx2
        rcases x1 with ⟨⟨⟨b1, l1⟩, m1⟩, r1⟩; rcases x2 with ⟨⟨⟨b2, l2⟩, m2⟩, r2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact Prod.ext (Prod.ext (Prod.ext (hx1.1.1.1.trans hx2.1.1.1.symm) rfl) rfl) rfl)
      (fun b x hx => by
        simp only [c_in, ci2, ci1, c0, stepOut, stepIn, condBase, p2Finset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨⟨hx.1.2, hx.2⟩, hx.1.1.1 ▸ hx.1.1.2⟩)
    have hent : c_out.ent + c_in.ent =
        H2 G 4 3 + H2 G 5 4 + 2 * H2 G 6 5 + 2 * H2 G 7 6 -
        H1 G 4 - H1 G 5 - 3 * H1 G 6 - H1 G 7 := by
      dsimp [c_out, co2, co1, c_in, ci2, ci1, c0]
      rw [stepOut_ent, stepOut_ent, stepOut_ent, stepOut_ent, stepOut_ent, stepIn_ent, condBase_ent]
      ring
    have hprod_pos : 0 < (p2Finset G).card * (p11InFinset G).card :=
      Nat.mul_pos hp2_pos h_p11_01.1
    have hprod_log := log_le_of_mul_le_pow (c := 4) (d := 6) hprod_pos hn_pos
      (by simpa using sixteen_mul_p2_mul_p11In_le G hG)
    have hp2_r : (0 : ℝ) < ((p2Finset G).card : ℝ) := Nat.cast_pos.mpr hp2_pos
    have hp11_r : (0 : ℝ) < ((p11InFinset G).card : ℝ) := Nat.cast_pos.mpr h_p11_01.1
    rw [Nat.cast_mul, Real.log_mul hp2_r.ne' hp11_r.ne'] at hprod_log
    dsimp [logN, log2] at hprod_log ⊢
    linarith [hle, hent, h_p11_76, hprod_log]

  -- Component 10: (c_in5, c_out5) (mult 1), P_{1,2} rooted at leaf attached at vertex 5
  have h_c5 : 2 * H2 G 4 3 + 2 * H2 G 5 4 + 3 * H2 G 6 5 + H2 G 7 6 -
      H1 G 3 - 2 * H1 G 4 - 3 * H1 G 5 - 2 * H1 G 6 ≤ 8 * logN - 8 * log2 := by
    let c0 := condBase G 5
    have hm0 := condBase_hasMarg G 5
    let co1 := stepOut G c0 id hm0 hadj54
    let co2 := stepOut G co1 Prod.snd (stepOut_hasMarg_snd G c0 id hm0 hadj54) hadj43
    let co3 := stepIn G co2 Prod.snd
      (stepOut_hasMarg_snd G co1 Prod.snd (stepOut_hasMarg_snd G c0 id hm0 hadj54) hadj43) hadj43
    let c_out := stepIn G co3 Prod.snd
      (stepIn_hasMarg_snd G co2 Prod.snd
        (stepOut_hasMarg_snd G co1 Prod.snd (stepOut_hasMarg_snd G c0 id hm0 hadj54) hadj43)
        hadj43) hadj54
    let ci1 := stepIn G c0 id hm0 hadj65
    let ci2 := stepOut G ci1 Prod.snd (stepIn_hasMarg_snd G c0 id hm0 hadj65) hadj65
    let ci3 := stepIn G ci2 Prod.snd
      (stepOut_hasMarg_snd G ci1 Prod.snd (stepIn_hasMarg_snd G c0 id hm0 hadj65) hadj65) hadj65
    let c_in := stepIn G ci3 Prod.snd
      (stepIn_hasMarg_snd G ci2 Prod.snd
        (stepOut_hasMarg_snd G ci1 Prod.snd (stepIn_hasMarg_snd G c0 id hm0 hadj65) hadj65)
        hadj65) hadj76
    let emb : (((W × W) × W) × W) × W → (W × W) × (W × W) :=
      fun p => ((p.1.1.1.2, p.1.1.2), (p.1.2, p.2))
    obtain ⟨hc_pos, hle⟩ := attached_pair_ent_le G hG hM c_out c_in
      (p12Finset G) emb emb (fun q => q.1.1)
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_out, co3, co2, co1, c0, stepIn, stepOut, condBase, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true] at hx1 hx2
        rcases x1 with ⟨⟨⟨⟨b1, a1⟩, bm1⟩, m1⟩, d1⟩
        rcases x2 with ⟨⟨⟨⟨b2, a2⟩, bm2⟩, m2⟩, d2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := heq
        exact Prod.ext (Prod.ext (Prod.ext (Prod.ext (hx1.1.1.1.1.trans hx2.1.1.1.1.symm) rfl)
          rfl) rfl) rfl)
      (fun b x hx => by
        simp only [c_out, co3, co2, co1, c0, stepIn, stepOut, condBase, p12Finset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨⟨hx.1.1.2, hx.1.2, hx.2⟩, hx.1.1.1.1 ▸ hx.1.1.1.2⟩)
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_in, ci3, ci2, ci1, c0, stepIn, stepOut, condBase, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true] at hx1 hx2
        rcases x1 with ⟨⟨⟨⟨b1, a1⟩, bm1⟩, m1⟩, d1⟩
        rcases x2 with ⟨⟨⟨⟨b2, a2⟩, bm2⟩, m2⟩, d2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := heq
        exact Prod.ext (Prod.ext (Prod.ext (Prod.ext (hx1.1.1.1.1.trans hx2.1.1.1.1.symm) rfl)
          rfl) rfl) rfl)
      (fun b x hx => by
        simp only [c_in, ci3, ci2, ci1, c0, stepIn, stepOut, condBase, p12Finset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨⟨hx.1.1.2, hx.1.2, hx.2⟩, hx.1.1.1.1 ▸ hx.1.1.1.2⟩)
    have hent : c_out.ent + c_in.ent =
        2 * H2 G 4 3 + 2 * H2 G 5 4 + 3 * H2 G 6 5 + H2 G 7 6 -
        H1 G 3 - 2 * H1 G 4 - 3 * H1 G 5 - 2 * H1 G 6 := by
      dsimp [c_out, co3, co2, co1, c_in, ci3, ci2, ci1, c0]
      rw [stepIn_ent, stepIn_ent, stepOut_ent, stepOut_ent,
          stepIn_ent, stepIn_ent, stepOut_ent, stepIn_ent, condBase_ent]
      ring
    have hcard := log_le_of_mul_le_pow (c := 3) (d := 4) hc_pos hn_pos
      (by simpa using eight_mul_card_p12_le G hG)
    dsimp [logN, log2] at hcard ⊢
    linarith [hle, hent, hcard]

  -- Component 11: (d_in5, d_out5) (mult 1), cev(P_{1,2}) rooted at leaf attached at vertex 5
  have h_d5 : H2 G 4 3 + 3 * H2 G 5 4 + 2 * H2 G 6 5 + 2 * H2 G 7 6 -
      2 * H1 G 4 - 3 * H1 G 5 - 2 * H1 G 6 - H1 G 7 ≤ 8 * logN - 8 * log2 := by
    let c0 := condBase G 5
    have hm0 := condBase_hasMarg G 5
    let co1 := stepOut G c0 id hm0 hadj54
    let co2 := stepIn G co1 Prod.snd (stepOut_hasMarg_snd G c0 id hm0 hadj54) hadj54
    let co3 := stepOut G co2 Prod.snd
      (stepIn_hasMarg_snd G co1 Prod.snd (stepOut_hasMarg_snd G c0 id hm0 hadj54) hadj54) hadj54
    let c_out := stepOut G co3 Prod.snd
      (stepOut_hasMarg_snd G co2 Prod.snd
        (stepIn_hasMarg_snd G co1 Prod.snd (stepOut_hasMarg_snd G c0 id hm0 hadj54) hadj54)
        hadj54) hadj43
    let ci1 := stepIn G c0 id hm0 hadj65
    let ci2 := stepIn G ci1 Prod.snd (stepIn_hasMarg_snd G c0 id hm0 hadj65) hadj76
    let ci3 := stepOut G ci2 Prod.snd
      (stepIn_hasMarg_snd G ci1 Prod.snd (stepIn_hasMarg_snd G c0 id hm0 hadj65) hadj76) hadj76
    let c_in := stepOut G ci3 Prod.snd
      (stepOut_hasMarg_snd G ci2 Prod.snd
        (stepIn_hasMarg_snd G ci1 Prod.snd (stepIn_hasMarg_snd G c0 id hm0 hadj65) hadj76)
        hadj76) hadj65
    let emb : (((W × W) × W) × W) × W → (W × W) × (W × W) :=
      fun p => ((p.1.1.1.2, p.1.1.2), (p.1.2, p.2))
    obtain ⟨hc_pos, hle⟩ := attached_pair_ent_le G hG hM c_out c_in
      (p12RevFinset G) emb emb (fun q => q.1.1)
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_out, co3, co2, co1, c0, stepOut, stepIn, condBase, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true] at hx1 hx2
        rcases x1 with ⟨⟨⟨⟨b1, a1⟩, bm1⟩, m1⟩, d1⟩
        rcases x2 with ⟨⟨⟨⟨b2, a2⟩, bm2⟩, m2⟩, d2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := heq
        exact Prod.ext (Prod.ext (Prod.ext (Prod.ext (hx1.1.1.1.1.trans hx2.1.1.1.1.symm) rfl)
          rfl) rfl) rfl)
      (fun b x hx => by
        simp only [c_out, co3, co2, co1, c0, stepOut, stepIn, condBase, p12RevFinset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨⟨hx.1.1.2, hx.1.2, hx.2⟩, hx.1.1.1.1 ▸ hx.1.1.1.2⟩)
      (fun b x1 hx1 x2 hx2 heq => by
        simp only [c_in, ci3, ci2, ci1, c0, stepOut, stepIn, condBase, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true] at hx1 hx2
        rcases x1 with ⟨⟨⟨⟨b1, a1⟩, bm1⟩, m1⟩, d1⟩
        rcases x2 with ⟨⟨⟨⟨b2, a2⟩, bm2⟩, m2⟩, d2⟩
        simp only [emb, Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := heq
        exact Prod.ext (Prod.ext (Prod.ext (Prod.ext (hx1.1.1.1.1.trans hx2.1.1.1.1.symm) rfl)
          rfl) rfl) rfl)
      (fun b x hx => by
        simp only [c_in, ci3, ci2, ci1, c0, stepOut, stepIn, condBase, p12RevFinset, emb,
          Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
          and_true, true_and] at hx ⊢
        exact ⟨⟨hx.1.1.2, hx.1.2, hx.2⟩, hx.1.1.1.1 ▸ hx.1.1.1.2⟩)
    have hent : c_out.ent + c_in.ent =
        H2 G 4 3 + 3 * H2 G 5 4 + 2 * H2 G 6 5 + 2 * H2 G 7 6 -
        2 * H1 G 4 - 3 * H1 G 5 - 2 * H1 G 6 - H1 G 7 := by
      dsimp [c_out, co3, co2, co1, c_in, ci3, ci2, ci1, c0]
      rw [stepOut_ent, stepOut_ent, stepIn_ent, stepOut_ent,
          stepOut_ent, stepOut_ent, stepIn_ent, stepIn_ent, condBase_ent]
      ring
    have hcard := log_le_of_mul_le_pow (c := 3) (d := 4) hc_pos hn_pos
      (by simpa using eight_mul_card_p12Rev_le G hG)
    dsimp [logN, log2] at hcard ⊢
    linarith [hle, hent, hcard]

  -- Slack at vertex 7 (mult 2)
  have h_v7 : H1 G 7 ≤ logN := H1_le_log_card G hM 7
  have h_kl := log_homCount_le_spider_ent G hM
  have h_log_main : Real.log ((d0Homs G).card : ℝ) ≤ 10 * logN - 9 * log2 := by
    linarith [h_kl, h_r01, h_d2, h_u0, h_u1, h_u4, h_y4, h_z4, h_w, h_xab, h_c5, h_d5, h_v7]
  -- Exponentiate to conclude ((d0Homs G).card : ℝ) / n^10 ≤ (1 / 2)^9
  have h_rhs_log : 10 * logN - 9 * log2 =
      Real.log (((1 / 2 : ℝ) ^ 9) * (Fintype.card W : ℝ) ^ 10) := by
    dsimp [logN, log2]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      one_div, Real.log_inv]
    ring
  rw [h_rhs_log] at h_log_main
  have h_exp := (Real.log_le_log_iff hM_r (by positivity)).mp h_log_main
  rw [div_le_iff₀ (pow_pos hn_r 10)]
  exact h_exp

end SandwichAssembly

end Spider234Proof

theorem OMA.solution : type_of% @SidorenkoConjecture.tournament_anti_sidorenko_spider234 := by
  classical
  intro V _ _ T _ hSpider
  obtain ⟨e, he_adj⟩ := Spider234Proof.spider_iso T hSpider
  let D : Digraph V :=
    { Adj := fun u v => Spider234Proof.D0.Adj (e.symm u) (e.symm v) }
  have hD_ori : D.IsOrientation T := by
    refine ⟨fun u v huv => ?_, fun u v huv => ?_⟩
    · have h1 := Spider234Proof.spiderDir_imp_undir (e.symm u) (e.symm v) huv
      have h2 := (he_adj (e.symm u) (e.symm v)).mpr h1
      simpa using h2
    · have h0 : T.Adj (e (e.symm u)) (e (e.symm v)) := by simpa using huv
      have h1 := (he_adj (e.symm u) (e.symm v)).mp h0
      exact Spider234Proof.spiderUndir_iff_dir (e.symm u) (e.symm v) h1
  refine ⟨D, hD_ori, fun {W} _ _ _ G _ hG => ?_⟩
  have hedge : T.edgeFinset.card = 9 := by
    have htree_edge := hSpider.1.card_edgeFinset
    have hcard := hSpider.2.1
    omega
  rw [hedge]
  refine le_of_eq_of_le ?_ (Spider234Proof.homCount_D0_bound G hG)
  unfold Digraph.homDensity Digraph.homCount
  have hV : Fintype.card V = Fintype.card (Fin 10) := by
    rw [hSpider.2.1, Fintype.card_fin]
  rw [hV]
  congr 2
  refine Fintype.card_congr ?_
  exact
    { toFun := fun φ =>
        { toFun := fun i => φ.toFun (e i)
          map_adj' := fun {i j} hij => by
            apply φ.map_adj'
            dsimp [D]
            simpa using hij }
      invFun := fun ψ =>
        { toFun := fun u => ψ.toFun (e.symm u)
          map_adj' := fun {u v} huv => ψ.map_adj' huv }
      left_inv := fun φ => by cases φ; dsimp; congr; ext u; simp
      right_inv := fun ψ => by cases ψ; dsimp; congr; ext i; simp }
