import FormalConjectures.ErdosProblems.«23»

-- Reduction Erdos23.erdos_23.variants.n5.R1 of Erdős Problem 23 — n5
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Reduction of the n = 5 case of Erdős Problem 23 to its residual middle range.

For a vertex set `S`, deleting the edges of `G` with both ends on the same side of `S` leaves a
bipartite subgraph, so it suffices to find `S` with at most 25 such edges.  Everything is proved
here except the residual case: a maximal triangle-free graph on 25 vertices (hence of diameter at
most 2) with 61 to 123 edges, all degrees at most 13, in which every neighbourhood cut deletes more
than 25 edges and every edge `uv` has fewer than `m - 51` edges inside `N(u) ∪ N(v)`.
* `H1`: the residual case with 61 to 92 edges.
* `H2`: the residual case with 93 to 123 edges.

Proved cases:
* at most 51 edges: averaging over all `2 ^ 25` cuts (`exists_half_cut`);
* 52 to 60 edges: the cut `N(u) | N(v)` of a well-chosen edge, the rest random (`sparse_ext`);
* at least 124 edges: the best neighbourhood cut plus Cauchy-Schwarz (`dense_case`);
* a vertex of degree at least 14: its neighbourhood cut plus Mantel (`highdeg_case`);
* a neighbourhood cut or an edge cut that already works (`cut_card_nbhd`, `exists_edge_cut_full`);
* adding edges never helps, so `G` may be taken maximal triangle-free (`exists_maximal_tf`),
  and then any two non-adjacent vertices have a common neighbour (`common_nbr_of_max`).
-/

namespace OMA.R_Erdos23_erdos_23_variants_n5_R1

open SimpleGraph Finset

open scoped Classical in
/-- The residual middle case with 61 to 92 edges. -/
def H1 : Prop :=
  ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj], G.CliqueFree 3 →
    (∀ H : SimpleGraph (Fin 25), G ≤ H → H.CliqueFree 3 → H = G) →
    (∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z) →
    61 ≤ G.edgeFinset.card → G.edgeFinset.card ≤ 92 → (∀ v, G.degree v ≤ 13) →
    (∀ v, 25 < (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e,
      (x ∈ G.neighborFinset v ↔ y ∈ G.neighborFinset v))).card) →
    (∀ u v, G.Adj u v → (G.edgeFinset.filter
      (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card + 51
        < G.edgeFinset.card) →
    ∃ S : Finset (Fin 25),
      (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 25

open scoped Classical in
/-- The residual middle case with 93 to 123 edges. -/
def H2 : Prop :=
  ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj], G.CliqueFree 3 →
    (∀ H : SimpleGraph (Fin 25), G ≤ H → H.CliqueFree 3 → H = G) →
    (∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z) →
    93 ≤ G.edgeFinset.card → G.edgeFinset.card ≤ 123 → (∀ v, G.degree v ≤ 13) →
    (∀ v, 25 < (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e,
      (x ∈ G.neighborFinset v ↔ y ∈ G.neighborFinset v))).card) →
    (∀ u v, G.Adj u v → (G.edgeFinset.filter
      (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card + 51
        < G.edgeFinset.card) →
    ∃ S : Finset (Fin 25),
      (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 25

section
variable {V : Type} [Fintype V] [DecidableEq V]

-- Throughout, `P S e` stands for: both ends of the edge `e` lie on the same side of `S`.

omit [Fintype V] in
lemma same_mk (S : Finset V) (u v : V) :
    (∀ x ∈ s(u, v), ∀ y ∈ s(u, v), (x ∈ S ↔ y ∈ S)) ↔ (u ∈ S ↔ v ∈ S) := by
  simp only [Sym2.mem_iff]
  constructor
  · intro h; exact h u (Or.inl rfl) v (Or.inr rfl)
  · rintro h x (rfl | rfl) y (rfl | rfl) <;> tauto

open scoped Classical in
lemma cut_graph (P : Finset V → Sym2 V → Prop) (hP : ∀ S u v, P S s(u, v) ↔ (u ∈ S ↔ v ∈ S))
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
      (G.edgeFinset \ H.edgeFinset).card = (G.edgeFinset.filter (P S)).card := by
  let H : SimpleGraph V :=
    { Adj := fun u v => G.Adj u v ∧ ¬ (u ∈ S ↔ v ∈ S)
      symm := ⟨fun u v h => ⟨h.1.symm, fun h' => h.2 h'.symm⟩⟩
      loopless := ⟨fun u h => h.2 Iff.rfl⟩ }
  have hH : ∀ u v, H.Adj u v ↔ (G.Adj u v ∧ ¬ (u ∈ S ↔ v ∈ S)) := fun _ _ => Iff.rfl
  refine ⟨H, fun u v h => ((hH u v).1 h).1, ?_, ?_⟩
  · refine ⟨Coloring.mk (fun v => if v ∈ S then (0 : Fin 2) else 1) ?_⟩
    intro u v h
    have h2 := ((hH u v).1 h).2
    clear h hH
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp_all
  · congr 1
    ext e
    induction e using Sym2.ind with
    | h x y =>
      simp only [Finset.mem_sdiff, mem_edgeFinset, mem_edgeSet, Finset.mem_filter, hP, hH]
      tauto

lemma count_same_pair (u v : V) (huv : u ≠ v) :
    2 * ((univ : Finset (Finset V)).filter (fun S => (u ∈ S ↔ v ∈ S))).card
      = 2 ^ Fintype.card V := by
  have hAB : ((univ : Finset (Finset V)).filter (fun S => (u ∈ S ↔ v ∈ S))).card
      = ((univ : Finset (Finset V)).filter (fun S => ¬ (u ∈ S ↔ v ∈ S))).card := by
    apply Finset.card_nbij' (fun S => symmDiff S {u}) (fun S => symmDiff S {u})
    · intro S hS
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, huv.symm, not_true_eq_false,
        and_false, or_false, false_and]
      tauto
    · intro S hS
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, huv.symm, not_true_eq_false,
        and_false, or_false, false_and]
      tauto
    · intro S _
      simp [symmDiff_symmDiff_cancel_right]
    · intro S _
      simp [symmDiff_symmDiff_cancel_right]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Finset V))) (fun S => (u ∈ S ↔ v ∈ S))
  rw [Finset.card_univ, Fintype.card_finset] at hsum
  omega

open scoped Classical in
lemma exists_half_cut (P : Finset V → Sym2 V → Prop)
    (hP : ∀ S u v, P S s(u, v) ↔ (u ∈ S ↔ v ∈ S)) (G : SimpleGraph V) [Fintype G.edgeSet] :
    ∃ S : Finset V, 2 * (G.edgeFinset.filter (P S)).card ≤ G.edgeFinset.card := by
  have key : ∑ S : Finset V, 2 * (G.edgeFinset.filter (P S)).card
      = ∑ S : Finset V, G.edgeFinset.card := by
    have h1 : ∀ e ∈ G.edgeFinset,
        2 * ((univ : Finset (Finset V)).filter (fun S => P S e)).card
          = 2 ^ Fintype.card V := by
      intro e he
      induction e using Sym2.ind with
      | h x y =>
        have hxy : x ≠ y := by
          rw [mem_edgeFinset, mem_edgeSet] at he
          exact he.ne
        simp only [hP]
        exact count_same_pair x y hxy
    calc ∑ S : Finset V, 2 * (G.edgeFinset.filter (P S)).card
        = ∑ S : Finset V, ∑ e ∈ G.edgeFinset, 2 * (if P S e then 1 else 0) := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [Finset.card_filter, Finset.mul_sum]
      _ = ∑ e ∈ G.edgeFinset, ∑ S : Finset V, 2 * (if P S e then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ e ∈ G.edgeFinset, 2 ^ Fintype.card V := by
          refine Finset.sum_congr rfl (fun e he => ?_)
          rw [← Finset.mul_sum, ← Finset.card_filter]
          exact h1 e he
      _ = ∑ S : Finset V, G.edgeFinset.card := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_finset,
            smul_eq_mul, smul_eq_mul, mul_comm]
  obtain ⟨S, -, hS⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty key.le
  exact ⟨S, hS⟩

open scoped Classical in
lemma cut_card_nbhd (P : Finset V → Sym2 V → Prop)
    (hP : ∀ S u v, P S s(u, v) ↔ (u ∈ S ↔ v ∈ S))
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (v : V) :
    (G.edgeFinset.filter (P (G.neighborFinset v))).card
      + ∑ u ∈ G.neighborFinset v, G.degree u = G.edgeFinset.card := by
  have hind : ∀ a ∈ G.neighborFinset v, ∀ b ∈ G.neighborFinset v, ¬ G.Adj a b := by
    intro a ha b hb hab
    rw [mem_neighborFinset] at ha hb
    exact hG {v, a, b} (is3Clique_triple_iff.2 ⟨ha, hb, hab⟩)
  have h1 : G.edgeFinset.filter (fun e => ¬ P (G.neighborFinset v) e)
      = (G.neighborFinset v).biUnion (fun u => G.incidenceFinset u) := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      simp only [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, hP, Finset.mem_biUnion,
        mem_incidenceFinset, mk'_mem_incidenceSet_iff]
      constructor
      · rintro ⟨hxy, hn⟩
        by_cases hx : x ∈ G.neighborFinset v
        · exact ⟨x, hx, hxy, Or.inl rfl⟩
        · have hy : y ∈ G.neighborFinset v := by tauto
          exact ⟨y, hy, hxy, Or.inr rfl⟩
      · rintro ⟨u, hu, hxy, rfl | rfl⟩
        · exact ⟨hxy, fun hiff => hind _ hu _ (hiff.1 hu) hxy⟩
        · exact ⟨hxy, fun hiff => hind _ (hiff.2 hu) _ hu hxy⟩
  have h2 : ((G.neighborFinset v).biUnion (fun u => G.incidenceFinset u)).card
      = ∑ u ∈ G.neighborFinset v, G.degree u := by
    rw [Finset.card_biUnion]
    · exact Finset.sum_congr rfl (fun u _ => card_incidenceFinset_eq_degree G u)
    · intro a ha b hb hab
      show Disjoint (G.incidenceFinset a) (G.incidenceFinset b)
      rw [Finset.disjoint_left]
      intro e hea heb
      rw [mem_incidenceFinset] at hea heb
      have hsub := G.incidenceSet_inter_incidenceSet_subset hab ⟨hea, heb⟩
      rw [Set.mem_singleton_iff] at hsub
      have hadj : G.Adj a b := by
        have := hea.1
        rw [hsub, mem_edgeSet] at this
        exact this
      exact hind a ha b hb hadj
  have h3 := Finset.card_filter_add_card_filter_not
    (s := G.edgeFinset) (fun e => P (G.neighborFinset v) e)
  rw [h1, h2] at h3
  exact h3

omit [DecidableEq V] in
lemma sum_nbhd_deg (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v, ∑ u ∈ G.neighborFinset v, G.degree u = ∑ u, G.degree u ^ 2 := by
  simp_rw [neighborFinset_eq_filter (G := G), Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, sq]
  congr 1
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  congr 1
  ext w
  simp [adj_comm]

end

open scoped Classical in
lemma dense_case (P : Finset (Fin 25) → Sym2 (Fin 25) → Prop)
    (hP : ∀ S u v, P S s(u, v) ↔ (u ∈ S ↔ v ∈ S))
    (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hm : 124 ≤ G.edgeFinset.card) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (P S)).card ≤ 25 := by
  by_contra hcon
  push Not at hcon
  have hv : ∀ v, 26 + ∑ u ∈ G.neighborFinset v, G.degree u ≤ G.edgeFinset.card := by
    intro v
    have h1 := cut_card_nbhd P hP G hG v
    have h2 := hcon (G.neighborFinset v)
    omega
  have hsum : ∑ v : Fin 25, (26 + ∑ u ∈ G.neighborFinset v, G.degree u)
      ≤ ∑ v : Fin 25, G.edgeFinset.card := Finset.sum_le_sum (fun v _ => hv v)
  rw [Finset.sum_add_distrib, sum_nbhd_deg] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin 25)))
    (f := fun v => G.degree v)
  rw [sum_degrees_eq_twice_card_edges] at hcs
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_id] at hcs
  set M := G.edgeFinset.card
  set D := ∑ u, G.degree u ^ 2
  have hM : (124 : ℤ) ≤ M := by exact_mod_cast hm
  have h1 : (650 : ℤ) + D ≤ 25 * M := by exact_mod_cast hsum
  have h2 : (2 * (M : ℤ)) ^ 2 ≤ 25 * D := by exact_mod_cast hcs
  nlinarith [sq_nonneg ((M : ℤ) - 124)]

section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma mem_eside (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (T : Finset V) (x : V) :
    x ∈ (T ∪ G.neighborFinset u) \ G.neighborFinset v
      ↔ ((x ∈ T ∨ x ∈ G.neighborFinset u) ∧ x ∉ G.neighborFinset v) := by
  simp only [Finset.mem_sdiff, Finset.mem_union]

lemma toggle_count (P : Finset V → Prop) [DecidablePred P] (x : V)
    (hP : ∀ T, P (symmDiff T {x}) ↔ ¬ P T) :
    2 * ((univ : Finset (Finset V)).filter P).card = 2 ^ Fintype.card V := by
  have hAB : ((univ : Finset (Finset V)).filter P).card
      = ((univ : Finset (Finset V)).filter (fun T => ¬ P T)).card := by
    apply Finset.card_nbij' (fun S => symmDiff S {x}) (fun S => symmDiff S {x})
    · intro S hS
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
      rw [hP]
      exact not_not.mpr hS
    · intro S hS
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
      rw [hP]
      exact hS
    · intro S _
      simp [symmDiff_symmDiff_cancel_right]
    · intro S _
      simp [symmDiff_symmDiff_cancel_right]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Finset V))) P
  rw [Finset.card_univ, Fintype.card_finset] at hsum
  omega

lemma nbhd_disj (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3) {u v : V}
    (huv : G.Adj u v) (x : V) (hxu : x ∈ G.neighborFinset u) : x ∉ G.neighborFinset v := by
  intro hxv
  rw [mem_neighborFinset] at hxu hxv
  exact hG {u, v, x} (is3Clique_triple_iff.2 ⟨huv, hxu, hxv⟩)

open scoped Classical in
lemma edge_count (P : Finset V → Sym2 V → Prop)
    (hP : ∀ S u v, P S s(u, v) ↔ (u ∈ S ↔ v ∈ S))
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v x y : V) (hxy : x ≠ y)
    (hx : x ∉ G.neighborFinset u) (hx' : x ∉ G.neighborFinset v) :
    2 * ((univ : Finset (Finset V)).filter
      (fun T => P ((T ∪ G.neighborFinset u) \ G.neighborFinset v) s(x, y))).card
      = 2 ^ Fintype.card V := by
  apply toggle_count _ x
  intro T
  have hyx : y ≠ x := hxy.symm
  simp only [hP, mem_eside, Finset.mem_symmDiff, Finset.mem_singleton, hyx, hx, hx',
    not_false_eq_true, and_true, or_false, true_and, false_and, and_false, false_or,
    not_true_eq_false]
  tauto

open scoped Classical in
lemma exists_edge_cut (P : Finset V → Sym2 V → Prop)
    (hP : ∀ S u v, P S s(u, v) ↔ (u ∈ S ↔ v ∈ S))
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3) {u v : V}
    (huv : G.Adj u v) :
    ∃ S : Finset V, 2 * (G.edgeFinset.filter (P S)).card + G.degree u + G.degree v
      ≤ G.edgeFinset.card + 1 := by
  set N := G.neighborFinset u ∪ G.neighborFinset v with hN
  set E0 := G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ N) with hE0
  set ER := G.edgeFinset.filter (fun e => ¬ ∀ x ∈ e, x ∈ N) with hER
  have hsplit : E0.card + ER.card = G.edgeFinset.card :=
    Finset.card_filter_add_card_filter_not _
  have hu : u ∈ N := by
    rw [hN, Finset.mem_union, mem_neighborFinset, mem_neighborFinset]
    exact Or.inr huv.symm
  have hv : v ∈ N := by
    rw [hN, Finset.mem_union, mem_neighborFinset, mem_neighborFinset]
    exact Or.inl huv
  have hNu : ∀ z, G.Adj u z → z ∈ N := by
    intro z hz
    rw [hN, Finset.mem_union, mem_neighborFinset]
    exact Or.inl hz
  have hNv : ∀ z, G.Adj v z → z ∈ N := by
    intro z hz
    rw [hN, Finset.mem_union, mem_neighborFinset, mem_neighborFinset]
    exact Or.inr hz
  have hinc : G.incidenceFinset u ∪ G.incidenceFinset v ⊆ E0 := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [Finset.mem_union, mem_incidenceFinset, mem_incidenceFinset,
        mk'_mem_incidenceSet_iff, mk'_mem_incidenceSet_iff] at he
      rw [hE0, Finset.mem_filter, mem_edgeFinset, mem_edgeSet]
      rcases he with ⟨hxy, hux | huy⟩ | ⟨hxy, hvx | hvy⟩
      · subst hux
        refine ⟨hxy, fun z hz => ?_⟩
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hu
        · exact hNu _ hxy
      · subst huy
        refine ⟨hxy, fun z hz => ?_⟩
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hNu _ hxy.symm
        · exact hu
      · subst hvx
        refine ⟨hxy, fun z hz => ?_⟩
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hv
        · exact hNv _ hxy
      · subst hvy
        refine ⟨hxy, fun z hz => ?_⟩
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hNv _ hxy.symm
        · exact hv
  have hinter : G.incidenceFinset u ∩ G.incidenceFinset v = {s(u, v)} := by
    ext e
    rw [Finset.mem_inter, mem_incidenceFinset, mem_incidenceFinset, Finset.mem_singleton]
    have hset := G.incidenceSet_inter_incidenceSet_of_adj huv
    constructor
    · intro h
      have h' : e ∈ G.incidenceSet u ∩ G.incidenceSet v := h
      rw [hset] at h'
      exact h'
    · intro h
      have h' : e ∈ ({s(u, v)} : Set (Sym2 V)) := h
      rw [← hset] at h'
      exact h'
  have hcard : (G.incidenceFinset u ∪ G.incidenceFinset v).card + 1
      = G.degree u + G.degree v := by
    have := Finset.card_union_add_card_inter (G.incidenceFinset u) (G.incidenceFinset v)
    rw [hinter, Finset.card_singleton, card_incidenceFinset_eq_degree,
      card_incidenceFinset_eq_degree] at this
    exact this
  have hzero : ∀ e ∈ G.edgeFinset, (∀ x ∈ e, x ∈ N) →
      ∀ T : Finset V, ¬ P ((T ∪ G.neighborFinset u) \ G.neighborFinset v) e := by
    intro e he hall T hs
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      rw [hP, mem_eside, mem_eside] at hs
      have hx := hall x (Sym2.mem_mk_left x y)
      have hy := hall y (Sym2.mem_mk_right x y)
      rw [hN, Finset.mem_union] at hx hy
      rcases hx with hxu | hxv
      · have hxv := nbhd_disj G hG huv x hxu
        rcases hy with hyu | hyv
        · rw [mem_neighborFinset] at hxu hyu
          exact hG {u, x, y} (is3Clique_triple_iff.2 ⟨hxu, hyu, he⟩)
        · have : ¬ ((y ∈ T ∨ y ∈ G.neighborFinset u) ∧ y ∉ G.neighborFinset v) :=
            fun h => h.2 hyv
          exact this (hs.1 ⟨Or.inr hxu, hxv⟩)
      · rcases hy with hyu | hyv
        · have hyv := nbhd_disj G hG huv y hyu
          have : ¬ ((x ∈ T ∨ x ∈ G.neighborFinset u) ∧ x ∉ G.neighborFinset v) :=
            fun h => h.2 hxv
          exact this (hs.2 ⟨Or.inr hyu, hyv⟩)
        · rw [mem_neighborFinset] at hxv hyv
          exact hG {v, x, y} (is3Clique_triple_iff.2 ⟨hxv, hyv, he⟩)
  have hcount : ∀ e ∈ G.edgeFinset,
      2 * ((univ : Finset (Finset V)).filter
        (fun T => P ((T ∪ G.neighborFinset u) \ G.neighborFinset v) e)).card
        = if (∀ x ∈ e, x ∈ N) then 0 else 2 ^ Fintype.card V := by
    intro e he
    split_ifs with hall
    · rw [Finset.filter_false_of_mem (fun T _ => hzero e he hall T)]
      simp
    · push Not at hall
      obtain ⟨x, hxe, hxN⟩ := hall
      have hspec := Sym2.other_spec hxe
      rw [← hspec] at he ⊢
      have hne : x ≠ Sym2.Mem.other hxe := by
        rw [mem_edgeFinset, mem_edgeSet] at he
        exact he.ne
      rw [hN, Finset.mem_union, not_or] at hxN
      exact edge_count P hP G u v x _ hne hxN.1 hxN.2
  have key : ∑ T : Finset V, 2 * (G.edgeFinset.filter
      (P ((T ∪ G.neighborFinset u) \ G.neighborFinset v))).card
      = ∑ T : Finset V, ER.card := by
    calc ∑ T : Finset V, 2 * (G.edgeFinset.filter
          (P ((T ∪ G.neighborFinset u) \ G.neighborFinset v))).card
        = ∑ T : Finset V, ∑ e ∈ G.edgeFinset,
            2 * (if P ((T ∪ G.neighborFinset u) \ G.neighborFinset v) e then 1 else 0) := by
          refine Finset.sum_congr rfl (fun T _ => ?_)
          rw [Finset.card_filter, Finset.mul_sum]
      _ = ∑ e ∈ G.edgeFinset, ∑ T : Finset V,
            2 * (if P ((T ∪ G.neighborFinset u) \ G.neighborFinset v) e then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ e ∈ G.edgeFinset, (if (∀ x ∈ e, x ∈ N) then 0 else 2 ^ Fintype.card V) := by
          refine Finset.sum_congr rfl (fun e he => ?_)
          rw [← Finset.mul_sum, ← Finset.card_filter]
          exact hcount e he
      _ = ∑ T : Finset V, ER.card := by
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.sum_const,
            Finset.card_univ, Fintype.card_finset, smul_eq_mul, smul_eq_mul, mul_comm]
  obtain ⟨T, -, hT⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty key.le
  refine ⟨(T ∪ G.neighborFinset u) \ G.neighborFinset v, ?_⟩
  have := Finset.card_le_card hinc
  omega

open scoped Classical in
lemma exists_edge_cut_full (P : Finset V → Sym2 V → Prop)
    (hP : ∀ S u v, P S s(u, v) ↔ (u ∈ S ↔ v ∈ S))
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    {u v : V} (huv : G.Adj u v) :
    ∃ S : Finset V, 2 * (G.edgeFinset.filter (P S)).card
      + (G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card
      ≤ G.edgeFinset.card := by
  set N := G.neighborFinset u ∪ G.neighborFinset v with hN
  set E0 := G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ N) with hE0
  set ER := G.edgeFinset.filter (fun e => ¬ ∀ x ∈ e, x ∈ N) with hER
  have hsplit : E0.card + ER.card = G.edgeFinset.card :=
    Finset.card_filter_add_card_filter_not _
  have hzero : ∀ e ∈ G.edgeFinset, (∀ x ∈ e, x ∈ N) →
      ∀ T : Finset V, ¬ P ((T ∪ G.neighborFinset u) \ G.neighborFinset v) e := by
    intro e he hall T hs
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      rw [hP, mem_eside, mem_eside] at hs
      have hx := hall x (Sym2.mem_mk_left x y)
      have hy := hall y (Sym2.mem_mk_right x y)
      rw [hN, Finset.mem_union] at hx hy
      rcases hx with hxu | hxv
      · have hxv := nbhd_disj G hG huv x hxu
        rcases hy with hyu | hyv
        · rw [mem_neighborFinset] at hxu hyu
          exact hG {u, x, y} (is3Clique_triple_iff.2 ⟨hxu, hyu, he⟩)
        · have : ¬ ((y ∈ T ∨ y ∈ G.neighborFinset u) ∧ y ∉ G.neighborFinset v) :=
            fun h => h.2 hyv
          exact this (hs.1 ⟨Or.inr hxu, hxv⟩)
      · rcases hy with hyu | hyv
        · have hyv := nbhd_disj G hG huv y hyu
          have : ¬ ((x ∈ T ∨ x ∈ G.neighborFinset u) ∧ x ∉ G.neighborFinset v) :=
            fun h => h.2 hxv
          exact this (hs.2 ⟨Or.inr hyu, hyv⟩)
        · rw [mem_neighborFinset] at hxv hyv
          exact hG {v, x, y} (is3Clique_triple_iff.2 ⟨hxv, hyv, he⟩)
  have hcount : ∀ e ∈ G.edgeFinset,
      2 * ((univ : Finset (Finset V)).filter
        (fun T => P ((T ∪ G.neighborFinset u) \ G.neighborFinset v) e)).card
        = if (∀ x ∈ e, x ∈ N) then 0 else 2 ^ Fintype.card V := by
    intro e he
    split_ifs with hall
    · rw [Finset.filter_false_of_mem (fun T _ => hzero e he hall T)]
      simp
    · push Not at hall
      obtain ⟨x, hxe, hxN⟩ := hall
      have hspec := Sym2.other_spec hxe
      rw [← hspec] at he ⊢
      have hne : x ≠ Sym2.Mem.other hxe := by
        rw [mem_edgeFinset, mem_edgeSet] at he
        exact he.ne
      rw [hN, Finset.mem_union, not_or] at hxN
      exact edge_count P hP G u v x _ hne hxN.1 hxN.2
  have key : ∑ T : Finset V, 2 * (G.edgeFinset.filter
      (P ((T ∪ G.neighborFinset u) \ G.neighborFinset v))).card
      = ∑ T : Finset V, ER.card := by
    calc ∑ T : Finset V, 2 * (G.edgeFinset.filter
          (P ((T ∪ G.neighborFinset u) \ G.neighborFinset v))).card
        = ∑ T : Finset V, ∑ e ∈ G.edgeFinset,
            2 * (if P ((T ∪ G.neighborFinset u) \ G.neighborFinset v) e then 1 else 0) := by
          refine Finset.sum_congr rfl (fun T _ => ?_)
          rw [Finset.card_filter, Finset.mul_sum]
      _ = ∑ e ∈ G.edgeFinset, ∑ T : Finset V,
            2 * (if P ((T ∪ G.neighborFinset u) \ G.neighborFinset v) e then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ e ∈ G.edgeFinset, (if (∀ x ∈ e, x ∈ N) then 0 else 2 ^ Fintype.card V) := by
          refine Finset.sum_congr rfl (fun e he => ?_)
          rw [← Finset.mul_sum, ← Finset.card_filter]
          exact hcount e he
      _ = ∑ T : Finset V, ER.card := by
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.sum_const,
            Finset.card_univ, Fintype.card_finset, smul_eq_mul, smul_eq_mul, mul_comm]
  obtain ⟨T, -, hT⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty key.le
  exact ⟨(T ∪ G.neighborFinset u) \ G.neighborFinset v, by omega⟩

end

lemma exists_good_edge (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hm : 1 ≤ G.edgeFinset.card) :
    ∃ u v, G.Adj u v ∧ 4 * G.edgeFinset.card ≤ 25 * (G.degree u + G.degree v) := by
  obtain ⟨u, -, hu⟩ := Finset.exists_max_image univ
    (fun u => ∑ w ∈ G.neighborFinset u, G.degree w) univ_nonempty
  have hS : ∑ v, ∑ w ∈ G.neighborFinset v, G.degree w
      ≤ 25 * ∑ w ∈ G.neighborFinset u, G.degree w := by
    calc ∑ v, ∑ w ∈ G.neighborFinset v, G.degree w
        ≤ ∑ v : Fin 25, ∑ w ∈ G.neighborFinset u, G.degree w :=
          Finset.sum_le_sum (fun v _ => hu v (mem_univ v))
      _ = 25 * ∑ w ∈ G.neighborFinset u, G.degree w := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [sum_nbhd_deg] at hS
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin 25)))
    (f := fun v => G.degree v)
  rw [sum_degrees_eq_twice_card_edges] at hcs
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_id] at hcs
  generalize hD : ∑ u, G.degree u ^ 2 = D at hS hcs
  generalize hM : G.edgeFinset.card = M at hm hcs ⊢
  by_cases hne : (G.neighborFinset u).Nonempty
  · obtain ⟨v, hv, hvmax⟩ :=
      Finset.exists_max_image (G.neighborFinset u) (fun w => G.degree w) hne
    have hSle : ∑ w ∈ G.neighborFinset u, G.degree w ≤ G.degree u * G.degree v := by
      calc ∑ w ∈ G.neighborFinset u, G.degree w
          ≤ ∑ w ∈ G.neighborFinset u, G.degree v := Finset.sum_le_sum (fun w hw => hvmax w hw)
        _ = G.degree u * G.degree v := by
            rw [Finset.sum_const, card_neighborFinset_eq_degree, smul_eq_mul]
    refine ⟨u, v, (mem_neighborFinset _ _ _).1 hv, ?_⟩
    generalize hSu : ∑ w ∈ G.neighborFinset u, G.degree w = Su at hS hSle
    generalize G.degree u = a at hSle ⊢
    generalize G.degree v = b at hSle ⊢
    have key : (4 * M) * (4 * M) ≤ (25 * (a + b)) * (25 * (a + b)) := by
      have h1 : (2 * (M : ℤ)) ^ 2 ≤ 25 * (D : ℤ) := by exact_mod_cast hcs
      have h2 : (D : ℤ) ≤ 25 * (Su : ℤ) := by exact_mod_cast hS
      have h3 : (Su : ℤ) ≤ (a : ℤ) * b := by exact_mod_cast hSle
      have : (4 * (M : ℤ)) * (4 * M) ≤ (25 * ((a : ℤ) + b)) * (25 * ((a : ℤ) + b)) := by
        nlinarith [sq_nonneg ((a : ℤ) - b)]
      exact_mod_cast this
    exact Nat.mul_self_le_mul_self_iff.1 key
  · exfalso
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hS
    have hD0 : D = 0 := by omega
    rw [hD0] at hcs
    simp at hcs
    omega

open scoped Classical in
lemma sparse_ext (P : Finset (Fin 25) → Sym2 (Fin 25) → Prop)
    (hP : ∀ S u v, P S s(u, v) ↔ (u ∈ S ↔ v ∈ S))
    (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (h1 : 52 ≤ G.edgeFinset.card) (h2 : G.edgeFinset.card ≤ 60) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (P S)).card ≤ 25 := by
  obtain ⟨u, v, huv, hdeg⟩ := exists_good_edge G (by omega)
  obtain ⟨S, hS⟩ := exists_edge_cut P hP G hG huv
  exact ⟨S, by omega⟩

open scoped Classical in
lemma highdeg_case (P : Finset (Fin 25) → Sym2 (Fin 25) → Prop)
    (hP : ∀ S u v, P S s(u, v) ↔ (u ∈ S ↔ v ∈ S))
    (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (v : Fin 25) (hv : 14 ≤ G.degree v) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (P S)).card ≤ 25 := by
  refine ⟨G.neighborFinset v, ?_⟩
  set W := (insert v (G.neighborFinset v))ᶜ with hWdef
  have hsub : G.edgeFinset.filter (P (G.neighborFinset v))
      ⊆ G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ W) := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, hP] at he
      rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet]
      refine ⟨he.1, fun z hz => ?_⟩
      have hxN : x ∉ G.neighborFinset v := by
        intro hx
        have hy := he.2.1 hx
        rw [mem_neighborFinset] at hx hy
        exact hG {v, x, y} (is3Clique_triple_iff.2 ⟨hx, hy, he.1⟩)
      have hyN : y ∉ G.neighborFinset v := fun hy => hxN (he.2.2 hy)
      have hxv : x ≠ v := by
        intro hxv
        subst hxv
        exact hyN ((mem_neighborFinset _ _ _).2 he.1)
      have hyv : y ≠ v := by
        intro hyv
        subst hyv
        exact hxN ((mem_neighborFinset _ _ _).2 he.1.symm)
      rw [Sym2.mem_iff] at hz
      rw [hWdef, Finset.mem_compl, Finset.mem_insert, not_or]
      rcases hz with rfl | rfl
      · exact ⟨hxv, hxN⟩
      · exact ⟨hyv, hyN⟩
  have hWcard : W.card ≤ 10 := by
    rw [hWdef, Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem
      (by simp), card_neighborFinset_eq_degree]
    omega
  have hmap : G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ W)
      ⊆ (G.induce (W : Set (Fin 25))).edgeFinset.map
        ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩ := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet] at he
      have hx : x ∈ W := he.2 x (Sym2.mem_mk_left x y)
      have hy : y ∈ W := he.2 y (Sym2.mem_mk_right x y)
      rw [Finset.mem_map]
      refine ⟨s(⟨x, hx⟩, ⟨y, hy⟩), ?_, ?_⟩
      · rw [mem_edgeFinset, mem_edgeSet, comap_adj]
        exact he.1
      · simp
  have hcf : (G.induce (W : Set (Fin 25))).CliqueFree 3 :=
    hG.comap (Embedding.induce _).isContained
  have hT := CliqueFree.card_edgeFinset_le (r := 2) hcf
  dsimp only at hT
  have hc : Fintype.card ↑(↑W : Set (Fin 25)) = W.card := by simp
  rw [hc] at hT
  have hbound : ∀ n : ℕ, n ≤ 10 →
      (n ^ 2 - (n % 2) ^ 2) * (2 - 1) / (2 * 2) + (n % 2).choose 2 ≤ 25 := by
    intro n hn
    interval_cases n <;> decide
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_le_card hmap
  rw [Finset.card_map] at h2
  have h3 := hbound _ hWcard
  omega

lemma exists_maximal_tf (G : SimpleGraph (Fin 25)) (hG : G.CliqueFree 3) :
    ∃ G' : SimpleGraph (Fin 25), G ≤ G' ∧ G'.CliqueFree 3 ∧
      ∀ H : SimpleGraph (Fin 25), G' ≤ H → H.CliqueFree 3 → H = G' := by
  obtain ⟨G', hle, hmax⟩ :=
    Finite.exists_le_maximal (p := fun H : SimpleGraph (Fin 25) => H.CliqueFree 3) hG
  exact ⟨G', hle, hmax.1, fun H hH hHcf => le_antisymm (hmax.2 hHcf hH) hH⟩

lemma common_nbr_of_max (G : SimpleGraph (Fin 25)) (hG : G.CliqueFree 3)
    (hmax : ∀ H : SimpleGraph (Fin 25), G ≤ H → H.CliqueFree 3 → H = G)
    (x y : Fin 25) (hxy : x ≠ y) (hn : ¬ G.Adj x y) : ∃ z, G.Adj x z ∧ G.Adj y z := by
  by_contra hno
  push Not at hno
  have hno' : ∀ z, G.Adj z x → G.Adj z y → False := fun z h1 h2 => hno z h1.symm h2.symm
  have hcf : (G ⊔ edge x y).CliqueFree 3 := by
    intro t ht
    rw [is3Clique_iff] at ht
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
    simp only [sup_adj, edge_adj] at hab hac hbc
    rcases hab with hab | ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, hab'⟩ <;>
    rcases hac with hac | ⟨⟨h3, h4⟩ | ⟨h3, h4⟩, hac'⟩ <;>
    rcases hbc with hbc | ⟨⟨h5, h6⟩ | ⟨h5, h6⟩, hbc'⟩ <;>
    subst_vars <;>
    first
      | exact hG {a, b, c} (is3Clique_triple_iff.2 ⟨hab, hac, hbc⟩)
      | exact absurd rfl hxy
      | exact absurd rfl hab'
      | exact absurd rfl hac'
      | exact absurd rfl hbc'
      | exact G.irrefl hab
      | exact G.irrefl hac
      | exact G.irrefl hbc
      | exact hno _ hab hac
      | exact hno _ hac hab
      | exact hno _ hab hac.symm
      | exact hno _ hac.symm hab
      | exact hno _ hab.symm hac
      | exact hno _ hac hab.symm
      | exact hno _ hab.symm hac.symm
      | exact hno _ hac.symm hab.symm
      | exact hno _ hab hbc
      | exact hno _ hbc hab
      | exact hno _ hab hbc.symm
      | exact hno _ hbc.symm hab
      | exact hno _ hab.symm hbc
      | exact hno _ hbc hab.symm
      | exact hno _ hab.symm hbc.symm
      | exact hno _ hbc.symm hab.symm
      | exact hno _ hac hbc
      | exact hno _ hbc hac
  have hle : G ≤ G ⊔ edge x y := le_sup_left
  have heq := hmax _ hle hcf
  apply hn
  have hadj : (G ⊔ edge x y).Adj x y := by
    rw [sup_adj, edge_adj]
    exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩
  rw [heq] at hadj
  exact hadj

open scoped Classical in
lemma filter_mono_graph (P : Finset (Fin 25) → Sym2 (Fin 25) → Prop)
    {G G' : SimpleGraph (Fin 25)} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (hle : G ≤ G') (S : Finset (Fin 25)) :
    (G.edgeFinset.filter (P S)).card ≤ (G'.edgeFinset.filter (P S)).card := by
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact edgeFinset_mono hle

open scoped Classical in
/-- The two hypotheses together give the residual middle case for an abstract same-side
predicate `P` that agrees with the explicit one. -/
lemma mid_of_hyps (h1 : H1) (h2 : H2) (P : Finset (Fin 25) → Sym2 (Fin 25) → Prop)
    (hPdef : ∀ S e, P S e ↔ ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S)) :
    ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj], G.CliqueFree 3 →
      (∀ H : SimpleGraph (Fin 25), G ≤ H → H.CliqueFree 3 → H = G) →
      (∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z) →
      61 ≤ G.edgeFinset.card → G.edgeFinset.card ≤ 123 → (∀ v, G.degree v ≤ 13) →
      (∀ v, 25 < (G.edgeFinset.filter (P (G.neighborFinset v))).card) →
      (∀ u v, G.Adj u v → (G.edgeFinset.filter
        (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card + 51
          < G.edgeFinset.card) →
      ∃ S : Finset (Fin 25), (G.edgeFinset.filter (P S)).card ≤ 25 := by
  intro G _ hG hmax hdiam hlo hhi hdeg hN hE
  have hfeq : ∀ S : Finset (Fin 25), G.edgeFinset.filter (P S)
      = G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S)) := by
    intro S
    ext e
    simp only [Finset.mem_filter, hPdef]
  have hN' : ∀ v, 25 < (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e,
      (x ∈ G.neighborFinset v ↔ y ∈ G.neighborFinset v))).card := by
    intro v
    rw [← hfeq]
    exact hN v
  by_cases hlow : G.edgeFinset.card ≤ 92
  · obtain ⟨S, hS⟩ := h1 G hG hmax hdiam hlo hlow hdeg hN' hE
    exact ⟨S, by rw [hfeq]; exact hS⟩
  · obtain ⟨S, hS⟩ := h2 G hG hmax hdiam (by omega) hhi hdeg hN' hE
    exact ⟨S, by rw [hfeq]; exact hS⟩

open scoped Classical in
lemma main_cut_max (P : Finset (Fin 25) → Sym2 (Fin 25) → Prop)
    (hP : ∀ S u v, P S s(u, v) ↔ (u ∈ S ↔ v ∈ S))
    (hmid : ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj], G.CliqueFree 3 →
      (∀ H : SimpleGraph (Fin 25), G ≤ H → H.CliqueFree 3 → H = G) →
      (∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z) →
      61 ≤ G.edgeFinset.card → G.edgeFinset.card ≤ 123 → (∀ v, G.degree v ≤ 13) →
      (∀ v, 25 < (G.edgeFinset.filter (P (G.neighborFinset v))).card) →
      (∀ u v, G.Adj u v → (G.edgeFinset.filter
        (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card + 51
          < G.edgeFinset.card) →
      ∃ S : Finset (Fin 25), (G.edgeFinset.filter (P S)).card ≤ 25)
    (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hmax : ∀ H : SimpleGraph (Fin 25), G ≤ H → H.CliqueFree 3 → H = G) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (P S)).card ≤ 25 := by
  by_cases hd : ∃ v, 14 ≤ G.degree v
  · obtain ⟨v, hv⟩ := hd
    exact highdeg_case P hP G hG v hv
  push Not at hd
  by_cases h1 : G.edgeFinset.card ≤ 51
  · obtain ⟨S, hS⟩ := exists_half_cut P hP G
    exact ⟨S, by omega⟩
  by_cases h3 : G.edgeFinset.card ≤ 60
  · exact sparse_ext P hP G hG (by omega) h3
  by_cases h2 : 124 ≤ G.edgeFinset.card
  · exact dense_case P hP G hG h2
  · by_cases hN : ∃ v, (G.edgeFinset.filter (P (G.neighborFinset v))).card ≤ 25
    · obtain ⟨v, hv⟩ := hN
      exact ⟨_, hv⟩
    push Not at hN
    by_cases hE : ∃ u v, G.Adj u v ∧ G.edgeFinset.card ≤ (G.edgeFinset.filter
        (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card + 51
    · obtain ⟨u, v, huv, hle⟩ := hE
      obtain ⟨S, hS⟩ := exists_edge_cut_full P hP G hG huv
      refine ⟨S, ?_⟩
      have hS' : 2 * (G.edgeFinset.filter (P S)).card
          + (G.edgeFinset.filter
            (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card
          ≤ G.edgeFinset.card := by convert hS
      omega
    push Not at hE
    exact hmid G hG hmax (common_nbr_of_max G hG hmax) (by omega) (by omega)
      (fun v => by have := hd v; omega) hN hE

open scoped Classical in
lemma main_cut (h1 : H1) (h2 : H2) (P : Finset (Fin 25) → Sym2 (Fin 25) → Prop)
    (hP : ∀ S u v, P S s(u, v) ↔ (u ∈ S ↔ v ∈ S))
    (hPdef : ∀ S e, P S e ↔ ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))
    (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (P S)).card ≤ 25 := by
  obtain ⟨G', hle, hG', hmax⟩ := exists_maximal_tf G hG
  obtain ⟨S, hS⟩ := main_cut_max P hP (mid_of_hyps h1 h2 P hPdef) G' hG' hmax
  exact ⟨S, le_trans (filter_mono_graph P hle S) hS⟩

theorem main : H1 → H2 → type_of% @Erdos23.erdos_23.variants.n5 := by
  intro h1 h2 G hG
  classical
  obtain ⟨S, hS⟩ := main_cut h1 h2 (fun S e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S)) same_mk
    (fun _ _ => Iff.rfl) G hG
  obtain ⟨H, hle, hbip, hcard⟩ :=
    cut_graph (fun S e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S)) same_mk G S
  refine ⟨H, hle, hbip, ?_⟩
  convert hcard.trans_le hS

end OMA.R_Erdos23_erdos_23_variants_n5_R1
