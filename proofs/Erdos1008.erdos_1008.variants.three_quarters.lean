import FormalConjectures.ErdosProblems.«1008»

/-! The complete bipartite construction rules out the three-quarters exponent. -/

open SimpleGraph
open scoped SimpleGraph

namespace OMA

lemma fourCycle_of_two_common_neighbors {A B : Type*}
    (G : SimpleGraph (A ⊕ B)) {a a' : A} {b b' : B}
    (ha : a ≠ a') (hb : b ≠ b')
    (hab : G.Adj (.inl a) (.inr b)) (hab' : G.Adj (.inl a) (.inr b'))
    (ha'b : G.Adj (.inl a') (.inr b)) (ha'b' : G.Adj (.inl a') (.inr b')) :
    cycleGraph 4 ⊑ G := by
  let f : Fin 4 → A ⊕ B := ![.inl a, .inr b, .inl a', .inr b']
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | exact False.elim ((show ¬ (cycleGraph 4).Adj _ _ from by decide) hij)
    | simpa [f] using hab
    | simpa [f] using hab.symm
    | simpa [f] using hab'
    | simpa [f] using hab'.symm
    | simpa [f] using ha'b
    | simpa [f] using ha'b.symm
    | simpa [f] using ha'b'
    | simpa [f] using ha'b'.symm

lemma degree_le_one_add_choose (d : ℕ) : d ≤ 1 + d.choose 2 := by
  cases d with
  | zero => simp
  | succ d =>
    rw [show (2 : ℕ) = Nat.succ 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]
    omega

lemma folkman_edge_bound {A B : Type*} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B)) (hG : G ≤ completeBipartiteGraph A B)
    (hfree : ¬ (cycleGraph 4 ⊑ G)) :
    G.edgeSet.ncard ≤ Fintype.card B + (Fintype.card A).choose 2 := by
  classical
  let left : Finset (A ⊕ B) := Finset.univ.map Function.Embedding.inl
  let right : Finset (A ⊕ B) := Finset.univ.map Function.Embedding.inr
  let neighbors (b : B) : Finset A := Finset.univ.filter fun a => G.Adj (.inl a) (.inr b)
  let pairs (b : B) : Finset (Finset A) := (neighbors b).powersetCard 2
  have hbip : G.IsBipartiteWith (left : Set (A ⊕ B)) (right : Set (A ⊕ B)) := by
    constructor
    · rw [Set.disjoint_left]
      intro x
      cases x <;> simp [left, right]
    · intro x y h
      have hc := hG h
      cases x <;> cases y <;> simp_all [left, right]
  have hdeg (b : B) : (neighbors b).card = G.degree (.inr b) := by
    have hmap : (neighbors b).map Function.Embedding.inl = G.neighborFinset (.inr b) := by
      ext x
      cases x with
      | inl a => simp [neighbors, adj_comm]
      | inr a =>
        have hn : ¬ G.Adj (.inr b) (.inr a) := fun h => by simpa using hG h
        simp [neighbors, hn]
    rw [← G.card_neighborFinset_eq_degree, ← hmap, Finset.card_map]
  have hsum : G.edgeSet.ncard = ∑ b, (neighbors b).card := by
    rw [← G.coe_edgeFinset, Set.ncard_coe_finset,
      ← isBipartiteWith_sum_degrees_eq_card_edges' hbip]
    simp only [right, Finset.sum_map]
    exact Finset.sum_congr rfl fun b _ => (hdeg b).symm
  have hdisj : ((Finset.univ : Finset B) : Set B).PairwiseDisjoint pairs := by
    intro b _ b' _ hbb'
    refine Finset.disjoint_left.mpr fun T hT hT' => hfree ?_
    obtain ⟨hTb, hTcard⟩ := Finset.mem_powersetCard.mp hT
    have hTb' := (Finset.mem_powersetCard.mp hT').1
    obtain ⟨a, a', haa', rfl⟩ := Finset.card_eq_two.mp hTcard
    refine fourCycle_of_two_common_neighbors G haa' hbb' ?_ ?_ ?_ ?_
    · exact (Finset.mem_filter.mp (hTb (by simp))).2
    · exact (Finset.mem_filter.mp (hTb' (by simp))).2
    · exact (Finset.mem_filter.mp (hTb (by simp))).2
    · exact (Finset.mem_filter.mp (hTb' (by simp))).2
  have hsub : (Finset.univ : Finset B).biUnion pairs ⊆
      (Finset.univ : Finset A).powersetCard 2 := by
    intro T hT
    obtain ⟨b, _, hTb⟩ := Finset.mem_biUnion.mp hT
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
      (Finset.mem_powersetCard.mp hTb).2⟩
  have hpairs : (∑ b, (neighbors b).card.choose 2) ≤ (Fintype.card A).choose 2 := by
    calc
      _ = ∑ b, (pairs b).card := by
        exact Finset.sum_congr rfl fun b _ => (Finset.card_powersetCard _ _).symm
      _ = ((Finset.univ : Finset B).biUnion pairs).card := (Finset.card_biUnion hdisj).symm
      _ ≤ ((Finset.univ : Finset A).powersetCard 2).card := Finset.card_le_card hsub
      _ = _ := by rw [Finset.card_powersetCard, Finset.card_univ]
  calc
    G.edgeSet.ncard = ∑ b, (neighbors b).card := hsum
    _ ≤ ∑ b, (1 + (neighbors b).card.choose 2) :=
      Finset.sum_le_sum fun b _ => degree_le_one_add_choose _
    _ = Fintype.card B + (∑ b, (neighbors b).card.choose 2) := by simp [Finset.sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_left hpairs _

lemma completeBipartite_ncard {A B : Type*} [Fintype A] [Fintype B] :
    (completeBipartiteGraph A B).edgeSet.ncard = Fintype.card A * Fintype.card B := by
  rw [edgeSet_completeBipartiteGraph, Set.ncard_range_of_injective]
  · simp [Nat.card_eq_fintype_card, Fintype.card_prod]
  · intro x y heq
    rcases Sym2.eq_iff.mp heq with h | h
    · exact Prod.ext (Sum.inl.inj h.1) (Sum.inr.inj h.2)
    · cases h.1

end OMA

theorem OMA.solution : type_of% @Erdos1008.erdos_1008.variants.three_quarters := by
  rintro ⟨c, hc, h⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / c)
  have hmpos : 0 < (m : ℝ) := lt_trans (by positivity : (0 : ℝ) < 2 / c) hm
  have hcm : 2 < c * (m : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hc).mp hm
  let G := completeBipartiteGraph (Fin (m ^ 4)) (Fin ((m ^ 4) ^ 2))
  obtain ⟨H, hHG, hfree, hlarge⟩ := h (Fin (m ^ 4) ⊕ Fin ((m ^ 4) ^ 2)) G
  have hbound : H.edgeSet.ncard ≤ 2 * m ^ 8 := by
    calc
      _ ≤ (m ^ 4) ^ 2 + (m ^ 4).choose 2 := by
        simpa only [Fintype.card_fin] using OMA.folkman_edge_bound H hHG hfree
      _ ≤ (m ^ 4) ^ 2 + (m ^ 4) ^ 2 := Nat.add_le_add_left (Nat.choose_le_pow _ _) _
      _ = _ := by ring
  have hcount : G.edgeSet.ncard = m ^ 12 := by
    dsimp only [G]
    rw [OMA.completeBipartite_ncard]
    simp only [Fintype.card_fin]
    ring
  have hpow : (G.edgeSet.ncard : ℝ) ^ (3 / 4 : ℝ) = (m : ℝ) ^ 9 := by
    rw [hcount, Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg m)]
    rw [show ((12 : ℕ) : ℝ) * (3 / 4) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hpow] at hlarge
  have hsmall : (H.edgeSet.ncard : ℝ) ≤ 2 * (m : ℝ) ^ 8 := by exact_mod_cast hbound
  have hcontradiction : 2 * (m : ℝ) ^ 8 < c * (m : ℝ) ^ 9 := by
    calc
      _ < (c * (m : ℝ)) * (m : ℝ) ^ 8 :=
        mul_lt_mul_of_pos_right hcm (pow_pos hmpos _)
      _ = _ := by ring
  exact hcontradiction.not_ge (hlarge.trans hsmall)