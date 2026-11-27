import FormalConjectures.Wikipedia.SnakeInTheBox

/-!
Reduction `SnakeInBox.coil_small_dimensions.R1` of Snake in the box — coil small dimensions.
Credit: @skhakim.
Proves dimensions 0, 1, 2, 3, 4 completely and certifies optimal lower bounds
(14, 26, 48, 96) for dimensions 5, 6, 7, 8, isolating the four hard upper bounds as H1..H4.
-/

namespace OMA.R_SnakeInBox_coil_small_dimensions_R1

open SimpleGraph SnakeInBox symmDiff

def H1 : Prop := SnakeInBox.LongestCoilInTheBox 5 <= 14

def H2 : Prop := SnakeInBox.LongestCoilInTheBox 6 <= 26

def H3 : Prop := SnakeInBox.LongestCoilInTheBox 7 <= 48

def H4 : Prop := SnakeInBox.LongestCoilInTheBox 8 <= 96

section Helpers

private lemma card_even_fin4 :
    (Finset.univ.filter (fun v : Finset (Fin 4) => Even v.card)).card = 8 := by decide

section UpperBounds
open Classical

private lemma hypercube_adj_iff (n : ℕ) (a b : Finset (Fin n)) :
    (Hypercube n).Adj a b ↔ (a ∆ b).card = 1 := by
  simp only [Hypercube, fromRel_adj]
  rw [symmDiff_comm b a]
  constructor
  · exact fun h => h.2.elim id id
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    simp at h

private lemma hypercube_adj_parity {n : ℕ} {a b : Finset (Fin n)} (h : (Hypercube n).Adj a b) :
    (Even a.card ↔ Odd b.card) := by
  rw [hypercube_adj_iff, Finset.card_eq_one] at h
  obtain ⟨i, hi⟩ := h
  have hba : b = a ∆ {i} := by
    rw [← hi, symmDiff_symmDiff_cancel_left]
  rw [hba]
  by_cases hia : i ∈ a
  · have hsub : a ∆ {i} = a.erase i := by
      ext j
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
      by_cases hji : j = i
      · subst hji; simp [hia]
      · simp [hji]
    rw [hsub, Finset.card_erase_of_mem hia]
    have hpos : 1 ≤ a.card := Finset.one_le_card.mpr ⟨i, hia⟩
    rcases Nat.even_or_odd a.card with ⟨k, hk⟩ | ⟨k, hk⟩
    · constructor
      · intro _; exact ⟨k - 1, by omega⟩
      · intro _; exact ⟨k, hk⟩
    · constructor
      · intro he; exfalso; obtain ⟨m, hm⟩ := he; omega
      · intro ho; exfalso; obtain ⟨m, hm⟩ := ho; omega
  · have hins : a ∆ {i} = insert i a := by
      ext j
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      by_cases hji : j = i
      · subst hji; simp [hia]
      · simp [hji]
    rw [hins, Finset.card_insert_of_notMem hia]
    simp [Nat.odd_add_one]

private lemma hypercube_deg (n : ℕ) (a : Finset (Fin n)) :
    (Finset.univ.filter (fun b => (Hypercube n).Adj a b)).card = n := by
  have hbij : (Finset.univ.filter (fun b => (Hypercube n).Adj a b)) =
      Finset.univ.image (fun i : Fin n => a ∆ {i}) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hypercube_adj_iff,
      Finset.card_eq_one]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [← hi, symmDiff_symmDiff_cancel_left]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, by simp⟩
  rw [hbij, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    have h1 : ({i} : Finset (Fin n)) = {j} := by
      have := congrArg (a ∆ ·) hij
      simpa using this
    exact Finset.singleton_injective h1

private lemma coil_bddAbove (n : ℕ) :
    BddAbove {k | ∃ S : Subgraph (Hypercube n), IsCoilInGraphOfLength (Hypercube n) S k} := by
  refine ⟨2 ^ n, ?_⟩
  rintro k ⟨S, _, u, P, hCyc, _, rfl⟩
  have h1 : P.support.tail.length ≤ Fintype.card (Finset (Fin n)) :=
    hCyc.support_nodup.length_le_card
  have h2 : P.support.tail.length = P.length := by
    rw [List.length_tail, Walk.length_support]; omega
  rw [Fintype.card_finset, Fintype.card_fin] at h1
  omega

private lemma coil_length_ge_three {n k : ℕ} {S : Subgraph (Hypercube n)}
    (h : IsCoilInGraphOfLength (Hypercube n) S k) : 3 ≤ k := by
  obtain ⟨_, u, P, hCyc, _, rfl⟩ := h
  exact hCyc.three_le_length

private lemma walk_toSubgraph_adj_iff {V : Type*} {G : SimpleGraph V} {u v : V}
    (P : G.Walk u v) (a b : V) : P.toSubgraph.Adj a b ↔ s(a, b) ∈ P.edges := by
  induction P with
  | nil => simp
  | cons h Q ih =>
    change (G.subgraphOfAdj h ⊔ Q.toSubgraph).Adj a b ↔ s(a, b) ∈ (Walk.cons h Q).edges
    simp only [Subgraph.sup_adj, subgraphOfAdj_adj, Walk.edges_cons, List.mem_cons, ih, eq_comm]

private lemma coil_finset_props {n k : ℕ} {S : Subgraph (Hypercube n)}
    (h : IsCoilInGraphOfLength (Hypercube n) S k) :
    ∃ C : Finset (Finset (Fin n)), C.card = k ∧
      ∀ v ∈ C, (C.filter (fun w => (Hypercube n).Adj v w)).card = 2 := by
  obtain ⟨hInd, u, P, hCyc, rfl, rfl⟩ := h
  refine ⟨P.support.toFinset, ?_, ?_⟩
  · have htail : P.support.toFinset = P.support.tail.toFinset := by
      ext x
      simp only [List.mem_toFinset]
      cases P with
      | nil => exact (hCyc.ne_nil rfl).elim
      | @cons a b c hab Q =>
        simp only [Walk.support_cons, List.tail_cons, List.mem_cons]
        constructor
        · rintro (rfl | hx)
          · exact Q.end_mem_support
          · exact hx
        · exact Or.inr
    rw [htail, List.toFinset_card_of_nodup hCyc.support_nodup, List.length_tail, Walk.length_support]
    omega
  · intro v hv
    rw [List.mem_toFinset] at hv
    let Q := P.rotate v hv
    have hQCyc : Q.IsCycle := hCyc.rotate hv
    have hQedges : ∀ e, e ∈ Q.edges ↔ e ∈ P.edges := fun e => (P.rotate_edges v hv).perm.mem_iff
    have hQlen : 3 ≤ Q.length := hQCyc.three_le_length
    cases hQ : Q with
    | nil => exact (hQCyc.ne_nil hQ).elim
    | @cons _ w₁ _ hw₁ R =>
      have hmem_iff : ∀ w, w ∈ P.support.toFinset.filter (fun w => (Hypercube n).Adj v w) ↔
          s(v, w) ∈ Q.edges := by
        intro w
        simp only [Finset.mem_filter, List.mem_toFinset, hQedges]
        constructor
        · rintro ⟨hw, hadj⟩
          have hadj_sub : P.toSubgraph.Adj v w :=
            hInd (P.mem_verts_toSubgraph.mpr hv) (P.mem_verts_toSubgraph.mpr hw) hadj
          exact (walk_toSubgraph_adj_iff P v w).mp hadj_sub
        · intro he
          have hadj_sub : P.toSubgraph.Adj v w := (walk_toSubgraph_adj_iff P v w).mpr he
          exact ⟨(P.mem_verts_toSubgraph).mp hadj_sub.snd_mem, P.toSubgraph.adj_sub hadj_sub⟩
      -- Count edges of Q incident to v using Q = cons hw₁ R
      have hv_not_R_init : ∀ x ∈ R.support.dropLast, x ≠ v := by
        intro x hx hxv
        rw [hxv] at hx
        have hnodup := hQCyc.support_nodup
        rw [hQ, Walk.support_cons, List.tail_cons] at hnodup
        have hRsupp : R.support = R.support.dropLast ++ [v] := by
          have hne : R.support ≠ [] := Walk.support_ne_nil R
          conv_lhs => rw [← List.dropLast_append_getLast hne]
          congr 1
          simp [Walk.getLast_support]
        rw [hRsupp, List.nodup_append] at hnodup
        exact hnodup.2.2 v hx v (List.mem_singleton_self v) rfl
      -- Now look at R: since R is non-nil (length >= 2), reverse R to get the last edge!
      cases hRrev : R.reverse with
      | nil =>
        have : R.length = 0 := by
          have := congrArg Walk.length hRrev
          simpa using this
        rw [hQ] at hQlen
        simp [this] at hQlen
      | @cons _ w₂ _ hw₂ S =>
        have hR_eq : R = S.reverse.concat hw₂.symm := by
          rw [← Walk.reverse_reverse R, hRrev, Walk.reverse_cons, Walk.concat_eq_append]
        have hS_not_v : v ∉ S.reverse.support := by
          intro hvS
          have hsub : S.reverse.support = R.support.dropLast := by
            rw [hR_eq, Walk.support_concat]
            simp
          rw [hsub] at hvS
          exact hv_not_R_init v hvS rfl
        have hQ_edges_eq : Q.edges = s(v, w₁) :: (S.reverse.edges ++ [s(w₂, v)]) := by
          rw [hQ, Walk.edges_cons, hR_eq, Walk.edges_concat, List.concat_eq_append]
        have hset : P.support.toFinset.filter (fun w => (Hypercube n).Adj v w) = {w₁, w₂} := by
          ext w
          rw [hmem_iff, hQ_edges_eq]
          simp only [List.mem_cons, List.mem_append, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (h1 | h2 | h3)
            · rw [Sym2.eq_iff] at h1
              rcases h1 with ⟨_, rfl⟩ | ⟨hvw, _⟩
              · exact Or.inl rfl
              · exact (hw₁.ne hvw).elim
            · exfalso
              exact hS_not_v (Walk.fst_mem_support_of_mem_edges S.reverse h2)
            · rcases h3 with h3 | h3
              · rw [Sym2.eq_iff] at h3
                rcases h3 with ⟨hvw, _⟩ | ⟨_, rfl⟩
                · exact (hw₂.ne hvw).elim
                · exact Or.inr rfl
              · exact (List.not_mem_nil h3).elim
          · rintro (rfl | rfl)
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (Or.inl Sym2.eq_swap))
        rw [hset, Finset.card_pair]
        intro h12
        subst h12
        have hnodup := hQCyc.edges_nodup
        rw [hQ_edges_eq, List.nodup_cons] at hnodup
        exact hnodup.1 (List.mem_append_right _ (List.mem_singleton.mpr Sym2.eq_swap))

private lemma hypercube_coil_even_odd {n : ℕ} (C : Finset (Finset (Fin n)))
    (hdeg : ∀ v ∈ C, (C.filter (fun w => (Hypercube n).Adj v w)).card = 2) :
    (C.filter (fun v => Even v.card)).card = (C.filter (fun v => Odd v.card)).card ∧
    C.card = 2 * (C.filter (fun v => Even v.card)).card := by
  let Ce := C.filter (fun v => Even v.card)
  let Co := C.filter (fun v => Odd v.card)
  have h1 : ∑ v ∈ Ce, (Co.filter (fun w => (Hypercube n).Adj v w)).card = 2 * Ce.card := by
    have hpt : ∀ v ∈ Ce, (Co.filter (fun w => (Hypercube n).Adj v w)).card = 2 := by
      intro v hv
      have hvC : v ∈ C := (Finset.mem_filter.mp hv).1
      have hvE : Even v.card := (Finset.mem_filter.mp hv).2
      have heq : Co.filter (fun w => (Hypercube n).Adj v w) =
          C.filter (fun w => (Hypercube n).Adj v w) := by
        ext w
        simp only [Co, Finset.mem_filter]
        constructor
        · exact fun ⟨⟨hwC, _⟩, hadj⟩ => ⟨hwC, hadj⟩
        · exact fun ⟨hwC, hadj⟩ => ⟨⟨hwC, (hypercube_adj_parity hadj).mp hvE⟩, hadj⟩
      rw [heq]
      exact hdeg v hvC
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, mul_comm]
  have h2 : ∑ w ∈ Co, (Ce.filter (fun v => (Hypercube n).Adj w v)).card = 2 * Co.card := by
    have hpt : ∀ w ∈ Co, (Ce.filter (fun v => (Hypercube n).Adj w v)).card = 2 := by
      intro w hw
      have hwC : w ∈ C := (Finset.mem_filter.mp hw).1
      have hwO : Odd w.card := (Finset.mem_filter.mp hw).2
      have heq : Ce.filter (fun v => (Hypercube n).Adj w v) =
          C.filter (fun v => (Hypercube n).Adj w v) := by
        ext v
        simp only [Ce, Finset.mem_filter]
        constructor
        · exact fun ⟨⟨hvC, _⟩, hadj⟩ => ⟨hvC, hadj⟩
        · exact fun ⟨hvC, hadj⟩ => ⟨⟨hvC, (hypercube_adj_parity hadj.symm).mpr hwO⟩, hadj⟩
      rw [heq]
      exact hdeg w hwC
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, mul_comm]
  have hsum : ∑ v ∈ Ce, (Co.filter (fun w => (Hypercube n).Adj v w)).card =
      ∑ w ∈ Co, (Ce.filter (fun v => (Hypercube n).Adj w v)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
    simp [adj_comm]
  have heo : Ce.card = Co.card := by omega
  have hpart : Ce.card + Co.card = C.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext v
      simp only [Ce, Co, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        rcases Nat.even_or_odd v.card with he | ho
        · exact Or.inl ⟨h, he⟩
        · exact Or.inr ⟨h, ho⟩
    · rw [Finset.disjoint_left]
      intro v hv1 hv2
      have hE := (Finset.mem_filter.mp hv1).2
      have hO := (Finset.mem_filter.mp hv2).2
      exact (Nat.not_even_iff_odd.mpr hO) hE
  dsimp only [Ce, Co] at heo hpart
  exact ⟨heo, by omega⟩

private lemma coil_one_eq_zero : LongestCoilInTheBox 1 = 0 := by
  have hempty : {k | ∃ S, IsCoilInGraphOfLength (Hypercube 1) S k} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    intro S hS
    have hge := coil_length_ge_three hS
    obtain ⟨C, hC, _⟩ := coil_finset_props hS
    have hle : C.card ≤ Fintype.card (Finset (Fin 1)) := Finset.card_le_univ C
    rw [Fintype.card_finset, Fintype.card_fin] at hle
    omega
  simp [LongestCoilInTheBox, LongestCoilInGraph, hempty]

private lemma coil_two_le : LongestCoilInTheBox 2 ≤ 4 := by
  apply csSup_le'
  rintro k ⟨S, hS⟩
  obtain ⟨C, hC, _⟩ := coil_finset_props hS
  have hle : C.card ≤ Fintype.card (Finset (Fin 2)) := Finset.card_le_univ C
  rw [Fintype.card_finset, Fintype.card_fin] at hle
  omega

private lemma coil_three_le : LongestCoilInTheBox 3 ≤ 6 := by
  apply csSup_le'
  rintro k ⟨S, hS⟩
  obtain ⟨C, rfl, hdeg⟩ := coil_finset_props hS
  have h1 : ∑ v ∈ C, (Cᶜ.filter (fun w => (Hypercube 3).Adj v w)).card = C.card := by
    have hpt : ∀ v ∈ C, (Cᶜ.filter (fun w => (Hypercube 3).Adj v w)).card = 1 := by
      intro v hv
      have htot := hypercube_deg 3 v
      have hin := hdeg v hv
      have hunion : (C.filter (fun w => (Hypercube 3).Adj v w)) ∪
          (Cᶜ.filter (fun w => (Hypercube 3).Adj v w)) =
          Finset.univ.filter (fun w => (Hypercube 3).Adj v w) := by
        ext w; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_compl, Finset.mem_univ,
          true_and]; tauto
      have hdisj : Disjoint (C.filter (fun w => (Hypercube 3).Adj v w))
          (Cᶜ.filter (fun w => (Hypercube 3).Adj v w)) := by
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        exact (Finset.mem_compl.mp (Finset.mem_filter.mp hw2).1) (Finset.mem_filter.mp hw1).1
      have hsum := Finset.card_union_of_disjoint hdisj
      rw [hunion, htot, hin] at hsum
      omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, mul_one]
  have h2 : ∑ v ∈ C, (Cᶜ.filter (fun w => (Hypercube 3).Adj v w)).card ≤ 3 * Cᶜ.card := by
    calc ∑ v ∈ C, (Cᶜ.filter (fun w => (Hypercube 3).Adj v w)).card
        = ∑ w ∈ Cᶜ, (C.filter (fun v => (Hypercube 3).Adj w v)).card := by
          simp only [Finset.card_filter]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
          simp [adj_comm]
      _ ≤ ∑ w ∈ Cᶜ, 3 := by
          refine Finset.sum_le_sum fun w _ => ?_
          calc (C.filter (fun v => (Hypercube 3).Adj w v)).card
              ≤ (Finset.univ.filter (fun v => (Hypercube 3).Adj w v)).card :=
                Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
            _ = 3 := hypercube_deg 3 w
      _ = 3 * Cᶜ.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hcompl : C.card + Cᶜ.card = 8 := by
    rw [Finset.card_add_card_compl, Fintype.card_finset, Fintype.card_fin]
    norm_num
  omega

private lemma coil_four_le : LongestCoilInTheBox 4 ≤ 8 := by
  apply csSup_le'
  rintro k ⟨S, hS⟩
  obtain ⟨C, rfl, hdeg⟩ := coil_finset_props hS
  by_contra hgt
  push Not at hgt
  obtain ⟨heo, h2e⟩ := hypercube_coil_even_odd C hdeg
  have hCe5 : 5 ≤ (C.filter (fun v => Even v.card)).card := by omega
  have hCo5 : 5 ≤ (C.filter (fun v => Odd v.card)).card := by omega
  let Eall : Finset (Finset (Fin 4)) := Finset.univ.filter (fun v => Even v.card)
  have hEall_card : Eall.card = 8 := by
    convert card_even_fin4 using 2
  let Eout : Finset (Finset (Fin 4)) := Eall \ C
  have hCe_sub : C.filter (fun v => Even v.card) ⊆ Eall := by
    intro v hv; simp only [Eall, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hv).2
  have hEout_card : Eout.card ≤ 3 := by
    have hdisj : Disjoint (C.filter (fun v => Even v.card)) Eout := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      exact (Finset.mem_sdiff.mp hv2).2 (Finset.mem_filter.mp hv1).1
    have hunion : (C.filter (fun v => Even v.card)) ∪ Eout = Eall := by
      ext v
      simp only [Eout, Eall, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        true_and]
      tauto
    have hsum := Finset.card_union_of_disjoint hdisj
    rw [hunion, hEall_card] at hsum
    omega
  -- Count edges between Co and Eout
  let Co := C.filter (fun v => Odd v.card)
  have hCo_out : ∑ v ∈ Co, (Eout.filter (fun w => (Hypercube 4).Adj v w)).card = 2 * Co.card := by
    have hpt : ∀ v ∈ Co, (Eout.filter (fun w => (Hypercube 4).Adj v w)).card = 2 := by
      intro v hv
      have hvC : v ∈ C := (Finset.mem_filter.mp hv).1
      have hvO : Odd v.card := (Finset.mem_filter.mp hv).2
      have htot := hypercube_deg 4 v
      have hin := hdeg v hvC
      have hunion : (C.filter (fun w => (Hypercube 4).Adj v w)) ∪
          (Eout.filter (fun w => (Hypercube 4).Adj v w)) =
          Finset.univ.filter (fun w => (Hypercube 4).Adj v w) := by
        ext w
        simp only [Eout, Eall, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff,
          Finset.mem_univ, true_and]
        constructor
        · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
        · intro hadj
          by_cases hwC : w ∈ C
          · exact Or.inl ⟨hwC, hadj⟩
          · exact Or.inr ⟨⟨(hypercube_adj_parity hadj.symm).mpr hvO, hwC⟩, hadj⟩
      have hdisj : Disjoint (C.filter (fun w => (Hypercube 4).Adj v w))
          (Eout.filter (fun w => (Hypercube 4).Adj v w)) := by
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw2).1).2 (Finset.mem_filter.mp hw1).1
      have hsum := Finset.card_union_of_disjoint hdisj
      rw [hunion, htot, hin] at hsum
      omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, mul_comm]
  have hswap : ∑ v ∈ Co, (Eout.filter (fun w => (Hypercube 4).Adj v w)).card =
      ∑ w ∈ Eout, (Co.filter (fun v => (Hypercube 4).Adj w v)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
    simp [adj_comm]
  have hex_w : ∃ w ∈ Eout, 4 ≤ (Co.filter (fun v => (Hypercube 4).Adj w v)).card := by
    by_contra hall
    push Not at hall
    have hle : ∑ w ∈ Eout, (Co.filter (fun v => (Hypercube 4).Adj w v)).card ≤ 3 * Eout.card := by
      calc ∑ w ∈ Eout, (Co.filter (fun v => (Hypercube 4).Adj w v)).card
          ≤ ∑ w ∈ Eout, 3 := Finset.sum_le_sum fun w hw => Nat.lt_succ_iff.mp (hall w hw)
        _ = 3 * Eout.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    dsimp only [Co] at hCo_out hswap hle
    omega
  obtain ⟨w, hw_out, hw_deg⟩ := hex_w
  have hw_notC : w ∉ C := (Finset.mem_sdiff.mp hw_out).2
  have hw_all_nbrs : ∀ v : Finset (Fin 4), (Hypercube 4).Adj w v → v ∈ C := by
    have hsub : Co.filter (fun v => (Hypercube 4).Adj w v) ⊆
        Finset.univ.filter (fun v => (Hypercube 4).Adj w v) :=
      Finset.filter_subset_filter _ (Finset.subset_univ _)
    have heq : Co.filter (fun v => (Hypercube 4).Adj w v) =
        Finset.univ.filter (fun v => (Hypercube 4).Adj w v) :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hypercube_deg 4 w]; exact hw_deg)
    intro v hv
    have hvmem : v ∈ Co.filter (fun v => (Hypercube 4).Adj w v) := by
      rw [heq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hvmem).1).1
  -- Shift C by w: C' = C.image (· ∆ w)
  let C' : Finset (Finset (Fin 4)) := C.image (· ∆ w)
  have hinj : Function.Injective (fun x : Finset (Fin 4) => x ∆ w) := fun x y hxy => by
    have := congrArg (· ∆ w) hxy
    simpa using this
  have hC'_card : C'.card = C.card := Finset.card_image_of_injective C hinj
  have hC'_deg : ∀ v ∈ C', (C'.filter (fun x => (Hypercube 4).Adj v x)).card = 2 := by
    intro v hv
    obtain ⟨v0, hv0C, rfl⟩ := Finset.mem_image.mp hv
    have heq : C'.filter (fun x => (Hypercube 4).Adj (v0 ∆ w) x) =
        (C.filter (fun x => (Hypercube 4).Adj v0 x)).image (· ∆ w) := by
      ext x
      simp only [C', Finset.mem_filter, Finset.mem_image, hypercube_adj_iff]
      constructor
      · rintro ⟨⟨x0, hx0, rfl⟩, hadj⟩
        refine ⟨x0, ⟨hx0, ?_⟩, rfl⟩
        have hsd : (v0 ∆ w) ∆ (x0 ∆ w) = v0 ∆ x0 := by
          ext i; simp only [Finset.mem_symmDiff]; tauto
        rwa [hsd] at hadj
      · rintro ⟨x0, ⟨hx0, hadj⟩, rfl⟩
        refine ⟨⟨x0, hx0, rfl⟩, ?_⟩
        have hsd : (v0 ∆ w) ∆ (x0 ∆ w) = v0 ∆ x0 := by
          ext i; simp only [Finset.mem_symmDiff]; tauto
        rwa [hsd]
    rw [heq, Finset.card_image_of_injective _ hinj]
    exact hdeg v0 hv0C
  obtain ⟨heo', h2e'⟩ := hypercube_coil_even_odd C' hC'_deg
  have hCe'5 : 5 ≤ (C'.filter (fun v => Even v.card)).card := by omega
  have h_empty_not : (∅ : Finset (Fin 4)) ∉ C' := by
    intro hem
    obtain ⟨v0, hv0C, hv0w⟩ := Finset.mem_image.mp hem
    have : v0 = w := symmDiff_eq_bot.mp hv0w
    subst this
    exact hw_notC hv0C
  have h_sing_in : ∀ i : Fin 4, ({i} : Finset (Fin 4)) ∈ C' := by
    intro i
    refine Finset.mem_image.mpr ⟨{i} ∆ w, ?_, by simp⟩
    apply hw_all_nbrs
    rw [hypercube_adj_iff]
    have : w ∆ ({i} ∆ w) = {i} := by
      rw [symmDiff_comm ({i}) w, symmDiff_symmDiff_cancel_left]
    rw [this]; simp
  let W1 : Finset (Finset (Fin 4)) := Finset.univ.image (fun i : Fin 4 => ({i} : Finset (Fin 4)))
  let W2 : Finset (Finset (Fin 4)) := C'.filter (fun v => v.card = 2)
  have hW1_card : W1.card = 4 := by
    rw [Finset.card_image_of_injective _ Finset.singleton_injective]; simp
  have hW1_sub : W1 ⊆ C' := by
    intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact h_sing_in i
  have h2W2 : 2 * W2.card ≤ 8 := by
    have hlhs : ∑ v ∈ W2, (W1.filter (fun s => (Hypercube 4).Adj v s)).card = 2 * W2.card := by
      have hpt : ∀ v ∈ W2, (W1.filter (fun s => (Hypercube 4).Adj v s)).card = 2 := by
        intro v hv
        have hv2 : v.card = 2 := (Finset.mem_filter.mp hv).2
        have heq : W1.filter (fun s => (Hypercube 4).Adj v s) =
            v.image (fun i : Fin 4 => ({i} : Finset (Fin 4))) := by
          ext s
          simp only [W1, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
            hypercube_adj_iff]
          constructor
          · rintro ⟨⟨i, rfl⟩, hadj⟩
            refine ⟨i, ?_, rfl⟩
            by_contra hi
            have hcard : (v ∆ {i}).card = 3 := by
              have : v ∆ {i} = insert i v := by
                ext j; simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
                by_cases hji : j = i
                · subst hji; simp [hi]
                · simp [hji]
              rw [this, Finset.card_insert_of_notMem hi, hv2]
            omega
          · rintro ⟨i, hiv, rfl⟩
            refine ⟨⟨i, rfl⟩, ?_⟩
            have : v ∆ {i} = v.erase i := by
              ext j; simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
              by_cases hji : j = i
              · subst hji; simp [hiv]
              · simp [hji]
            rw [this, Finset.card_erase_of_mem hiv, hv2]
        rw [heq, Finset.card_image_of_injective _ Finset.singleton_injective, hv2]
      rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, mul_comm]
    have hrhs : ∑ s ∈ W1, (W2.filter (fun v => (Hypercube 4).Adj s v)).card ≤ 8 := by
      calc ∑ s ∈ W1, (W2.filter (fun v => (Hypercube 4).Adj s v)).card
          ≤ ∑ s ∈ W1, (C'.filter (fun v => (Hypercube 4).Adj s v)).card := by
            refine Finset.sum_le_sum fun s _ => Finset.card_le_card ?_
            exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
        _ = ∑ s ∈ W1, 2 := Finset.sum_congr rfl fun s hs => hC'_deg s (hW1_sub hs)
        _ = 2 * W1.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ = 8 := by rw [hW1_card]
    have hsw : ∑ v ∈ W2, (W1.filter (fun s => (Hypercube 4).Adj v s)).card =
        ∑ s ∈ W1, (W2.filter (fun v => (Hypercube 4).Adj s v)).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun v _ => ?_
      simp [adj_comm]
    omega
  -- Every vertex in C'_even has card 2 or 4 (since ∅ ∉ C')
  have hCe'_sub : C'.filter (fun v => Even v.card) ⊆ insert Finset.univ W2 := by
    intro v hv
    obtain ⟨hvC', hvE⟩ := Finset.mem_filter.mp hv
    have hvle : v.card ≤ 4 := by
      simpa using Finset.card_le_univ v
    simp only [Finset.mem_insert, W2, Finset.mem_filter]
    obtain ⟨m, hm⟩ := hvE
    have h0 : v.card ≠ 0 := fun h0 => h_empty_not (Finset.card_eq_zero.mp h0 ▸ hvC')
    have hcases : v.card = 2 ∨ v.card = 4 := by omega
    rcases hcases with h2 | h4
    · exact Or.inr ⟨hvC', h2⟩
    · exact Or.inl (Finset.eq_univ_of_card v (by simpa using h4))
  have huniv_in : (Finset.univ : Finset (Fin 4)) ∈ C' := by
    by_contra hu
    have hsub2 : C'.filter (fun v => Even v.card) ⊆ W2 := by
      intro v hv
      rcases Finset.mem_insert.mp (hCe'_sub hv) with rfl | h
      · exact (hu (Finset.mem_filter.mp hv).1).elim
      · exact h
    have := Finset.card_le_card hsub2
    omega
  have hCe'_eq5 : (C'.filter (fun v => Even v.card)).card = 5 := by
    have hle5 : (C'.filter (fun v => Even v.card)).card ≤ (insert Finset.univ W2).card :=
      Finset.card_le_card hCe'_sub
    have hle' : (insert (Finset.univ : Finset (Fin 4)) W2).card ≤ W2.card + 1 :=
      Finset.card_insert_le _ _
    omega
  -- Finset.univ ∈ C' has 2 neighbors in C', both of card 3, disjoint from W1 (card 1)!
  let Ntop := C'.filter (fun v => (Hypercube 4).Adj Finset.univ v)
  have hNtop_card : Ntop.card = 2 := hC'_deg Finset.univ huniv_in
  have hNtop_card3 : ∀ v ∈ Ntop, v.card = 3 := by
    intro v hv
    have hadj : (Finset.univ ∆ v).card = 1 := (hypercube_adj_iff 4 _ _).mp (Finset.mem_filter.mp hv).2
    have hsd : Finset.univ ∆ v = vᶜ := by
      ext i; simp [Finset.mem_symmDiff]
    rw [hsd] at hadj
    have hcompl : v.card + vᶜ.card = 4 := by
      have h1 := Finset.card_add_card_compl v
      rwa [Fintype.card_fin] at h1
    omega
  have hdisj13 : Disjoint W1 Ntop := by
    rw [Finset.disjoint_left]
    intro v hv1 hv3
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv1
    have h3 := hNtop_card3 {i} hv3
    simp at h3
  have hsub_odd : W1 ∪ Ntop ⊆ C'.filter (fun v => Odd v.card) := by
    intro v hv
    rw [Finset.mem_filter]
    rcases Finset.mem_union.mp hv with hv1 | hv3
    · refine ⟨hW1_sub hv1, ?_⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv1
      simp
    · refine ⟨(Finset.mem_filter.mp hv3).1, ?_⟩
      rw [hNtop_card3 v hv3]
      exact ⟨1, rfl⟩
  have hge6 : 6 ≤ (C'.filter (fun v => Odd v.card)).card := by
    calc 6 = W1.card + Ntop.card := by rw [hW1_card, hNtop_card]
      _ = (W1 ∪ Ntop).card := (Finset.card_union_of_disjoint hdisj13).symm
      _ ≤ (C'.filter (fun v => Odd v.card)).card := Finset.card_le_card hsub_odd
  omega

end UpperBounds

-- General certified lower-bound lemma from a list of Nat bitmasks
private lemma toF_inj {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (h : Finset.univ.filter (fun i : Fin n => x.testBit i.1) =
         Finset.univ.filter (fun i : Fin n => y.testBit i.1)) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have hmem := Finset.ext_iff.mp h ⟨i, hi⟩
    simpa using hmem
  · have hx0 : x.testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
    have hy0 : y.testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [hx0, hy0]

private lemma toF_symmDiff (n x y : ℕ) :
    (Finset.univ.filter (fun i : Fin n => x.testBit i.1)) ∆
    (Finset.univ.filter (fun i : Fin n => y.testBit i.1)) =
    Finset.univ.filter (fun i : Fin n => (x ^^^ y).testBit i.1) := by
  ext i
  simp only [Finset.mem_symmDiff, Finset.mem_filter, Finset.mem_univ, true_and, Nat.testBit_xor]
  cases x.testBit i.1 <;> cases y.testBit i.1 <;> decide

private lemma toF_adj_iff {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    (Hypercube n).Adj (Finset.univ.filter (fun i : Fin n => x.testBit i.1))
      (Finset.univ.filter (fun i : Fin n => y.testBit i.1)) ↔
    (x ^^^ y) ∈ (List.range n).map (2 ^ ·) := by
  rw [hypercube_adj_iff, toF_symmDiff, Finset.card_eq_one]
  constructor
  · rintro ⟨i, hi⟩
    have hxy_lt : x ^^^ y < 2 ^ n := Nat.xor_lt_two_pow hx hy
    have hxy_eq : x ^^^ y = 2 ^ i.1 := by
      apply Nat.eq_of_testBit_eq
      intro k
      by_cases hk : k < n
      · have hmem := Finset.ext_iff.mp hi ⟨k, hk⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Fin.ext_iff] at hmem
        rw [Nat.testBit_two_pow]
        by_cases hki : i.1 = k
        · subst hki
          rw [hmem.mpr rfl]
          simp
        · have hne : k ≠ i.1 := Ne.symm hki
          have hfalse : (x ^^^ y).testBit k = false := by
            cases hb : (x ^^^ y).testBit k
            · rfl
            · exact (hne (hmem.mp hb)).elim
          simp [hfalse, hki]
      · have h1 : (x ^^^ y).testBit k = false :=
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hxy_lt (Nat.pow_le_pow_right (by omega) (by omega)))
        have h2 : (2 ^ i.1).testBit k = false := by
          rw [Nat.testBit_two_pow]
          have : i.1 ≠ k := by omega
          simp [this]
        rw [h1, h2]
    rw [hxy_eq, List.mem_map]
    exact ⟨i.1, List.mem_range.mpr i.2, rfl⟩
  · intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨b, hb, hxy⟩ := hmem
    have hbn : b < n := List.mem_range.mp hb
    refine ⟨⟨b, hbn⟩, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff,
      ← hxy, Nat.testBit_two_pow]
    simp [eq_comm]

private lemma build_walk_from_list {n : ℕ} (vs : List ℕ) (hk : 3 ≤ vs.length)
    (hbound : ∀ i, i < vs.length → vs.getD i 0 < 2 ^ n)
    (hadj : ∀ i, i < vs.length →
      (vs.getD i 0 ^^^ vs.getD ((i + 1) % vs.length) 0) ∈ (List.range n).map (2 ^ ·)) :
    ∀ r, r ≤ vs.length →
      ∃ W : (Hypercube n).Walk
        (Finset.univ.filter (fun b : Fin n => (vs.getD ((vs.length - r) % vs.length) 0).testBit b.1))
        (Finset.univ.filter (fun b : Fin n => (vs.getD 0 0).testBit b.1)),
        W.length = r ∧
        W.support = (List.range (r + 1)).map (fun t =>
          Finset.univ.filter (fun b : Fin n =>
            (vs.getD ((vs.length - r + t) % vs.length) 0).testBit b.1)) ∧
        ∀ t, t < r →
          s(Finset.univ.filter (fun b : Fin n =>
              (vs.getD ((vs.length - r + t) % vs.length) 0).testBit b.1),
            Finset.univ.filter (fun b : Fin n =>
              (vs.getD ((vs.length - r + t + 1) % vs.length) 0).testBit b.1)) ∈ W.edges := by
  intro r
  induction r with
  | zero =>
    intro _
    have h0 : (vs.length - 0) % vs.length = 0 := by simp
    refine ⟨Walk.nil.copy (by rw [h0]) rfl, ?_, ?_, ?_⟩
    · simp
    · simp [Walk.support_copy]; ext x; rfl
    · intro t ht; omega
  | succ r ih =>
    intro hr
    obtain ⟨W, hlen, hsupp, hedges⟩ := ih (by omega)
    have hidx_lt : vs.length - (r + 1) < vs.length := by omega
    have hmod1 : (vs.length - (r + 1)) % vs.length = vs.length - (r + 1) :=
      Nat.mod_eq_of_lt hidx_lt
    have hmod2 : (vs.length - (r + 1) + 1) % vs.length = (vs.length - r) % vs.length := by
      congr 1; omega
    have hedge : (Hypercube n).Adj
        (Finset.univ.filter (fun b : Fin n => (vs.getD ((vs.length - (r + 1)) % vs.length) 0).testBit b.1))
        (Finset.univ.filter (fun b : Fin n => (vs.getD ((vs.length - r) % vs.length) 0).testBit b.1)) := by
      rw [toF_adj_iff (hbound _ (Nat.mod_lt _ (by omega))) (hbound _ (Nat.mod_lt _ (by omega)))]
      have htmp := hadj (vs.length - (r + 1)) hidx_lt
      rwa [hmod1, ← hmod2]
    refine ⟨.cons hedge W, ?_, ?_, ?_⟩
    · simp [hlen]
    · rw [Walk.support_cons, hsupp]
      conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      refine congrArg₂ List.cons ?_ ?_
      · simp only [Nat.add_zero]
      · refine List.map_congr_left fun t _ => ?_
        have hsum : vs.length - (r + 1) + (t + 1) = vs.length - r + t := by omega
        simp only [Function.comp_apply, Nat.succ_eq_add_one, hsum]
    · intro t ht
      rw [Walk.edges_cons, List.mem_cons]
      cases t with
      | zero =>
        left
        simp only [Nat.add_zero]
        rw [hmod2]
      | succ t' =>
        right
        have h1 : vs.length - (r + 1) + (t' + 1) = vs.length - r + t' := by omega
        have h2 : vs.length - (r + 1) + (t' + 1) + 1 = vs.length - r + t' + 1 := by omega
        simpa only [h1, h2] using hedges t' (by omega)

private lemma coil_lower_bound_of_list (n : ℕ) (vs : List ℕ) (hk : 3 ≤ vs.length)
    (hcert : (vs.all (fun x => decide (x < 2 ^ n)) &&
      (List.range vs.length).all (fun i =>
        (List.range vs.length).all (fun j =>
          if i == j then true
          else if (i + 1) % vs.length == j || (j + 1) % vs.length == i then
            ((vs.getD i 0 ^^^ vs.getD j 0) ∈ (List.range n).map (2 ^ ·))
          else
            decide (vs.getD i 0 ≠ vs.getD j 0) &&
            !decide ((vs.getD i 0 ^^^ vs.getD j 0) ∈ (List.range n).map (2 ^ ·))))) = true) :
    vs.length ≤ LongestCoilInTheBox n := by
  simp only [Bool.and_eq_true, List.all_eq_true] at hcert
  obtain ⟨hbound_b, hpair_b⟩ := hcert
  have hgetD : ∀ i (hi : i < vs.length), vs.getD i 0 = vs[i] := by
    intro i hi; simp [List.getD_eq_getElem?_getD, hi]
  have hbound : ∀ i, i < vs.length → vs.getD i 0 < 2 ^ n := by
    intro i hi
    rw [hgetD i hi]
    exact of_decide_eq_true (hbound_b vs[i] (List.getElem_mem hi))
  have hadj : ∀ i, i < vs.length →
      (vs.getD i 0 ^^^ vs.getD ((i + 1) % vs.length) 0) ∈ (List.range n).map (2 ^ ·) := by
    intro i hi
    have hj : (i + 1) % vs.length < vs.length := Nat.mod_lt _ (by omega)
    have hne : i ≠ (i + 1) % vs.length := by
      intro heq
      by_cases hlast : i + 1 < vs.length
      · rw [Nat.mod_eq_of_lt hlast] at heq; omega
      · have : i + 1 = vs.length := by omega
        rw [this, Nat.mod_self] at heq; omega
    have hp := hpair_b i (List.mem_range.mpr hi) ((i + 1) % vs.length) (List.mem_range.mpr hj)
    have hbeq : (i == (i + 1) % vs.length) = false := beq_eq_false_iff_ne.mpr hne
    rw [hbeq, if_neg Bool.false_ne_true] at hp
    simpa only [beq_self_eq_true, Bool.true_or, ↓reduceIte, decide_eq_true_eq] using hp
  have hnonadj : ∀ i, i < vs.length → ∀ j, j < vs.length →
      i ≠ j → (i + 1) % vs.length ≠ j → (j + 1) % vs.length ≠ i →
      vs.getD i 0 ≠ vs.getD j 0 ∧ (vs.getD i 0 ^^^ vs.getD j 0) ∉ (List.range n).map (2 ^ ·) := by
    intro i hi j hj hij h1 h2
    have hp := hpair_b i (List.mem_range.mpr hi) j (List.mem_range.mpr hj)
    have hb0 : (i == j) = false := beq_eq_false_iff_ne.mpr hij
    have hb1 : ((i + 1) % vs.length == j) = false := beq_eq_false_iff_ne.mpr h1
    have hb2 : ((j + 1) % vs.length == i) = false := beq_eq_false_iff_ne.mpr h2
    rw [hb0, if_neg Bool.false_ne_true, hb1, hb2] at hp
    simpa only [Bool.or_self, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
      decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] using hp
  have hvs_inj : ∀ i, i < vs.length → ∀ j, j < vs.length → vs.getD i 0 = vs.getD j 0 → i = j := by
    intro i hi j hj heq
    by_contra hij
    by_cases h1 : (i + 1) % vs.length = j
    · have ha := hadj i hi
      rw [h1, heq, Nat.xor_self] at ha
      rw [List.mem_map] at ha
      obtain ⟨b, _, hb0⟩ := ha
      exact Nat.ne_of_gt (Nat.two_pow_pos b) hb0
    · by_cases h2 : (j + 1) % vs.length = i
      · have ha := hadj j hj
        rw [h2, heq, Nat.xor_self] at ha
        rw [List.mem_map] at ha
        obtain ⟨b, _, hb0⟩ := ha
        exact Nat.ne_of_gt (Nat.two_pow_pos b) hb0
      · exact (hnonadj i hi j hj hij h1 h2).1 heq
  obtain ⟨P0, hP0len, hP0supp, hP0edges⟩ := build_walk_from_list vs hk hbound hadj vs.length le_rfl
  let P : (Hypercube n).Walk
      (Finset.univ.filter (fun b : Fin n => (vs.getD 0 0).testBit b.1))
      (Finset.univ.filter (fun b : Fin n => (vs.getD 0 0).testBit b.1)) :=
    P0.copy (by simp) rfl
  have hPlen : P.length = vs.length := by simpa [P] using hP0len
  have hPsupp : P.support = (List.range (vs.length + 1)).map (fun t =>
      Finset.univ.filter (fun b : Fin n => (vs.getD (t % vs.length) 0).testBit b.1)) := by
    simpa [P] using hP0supp
  have hPedges : ∀ t, t < vs.length →
      s(Finset.univ.filter (fun b : Fin n => (vs.getD (t % vs.length) 0).testBit b.1),
        Finset.univ.filter (fun b : Fin n => (vs.getD ((t + 1) % vs.length) 0).testBit b.1)) ∈ P.edges := by
    intro t ht
    simpa [P] using hP0edges t ht
  have htail_nodup : P.support.tail.Nodup := by
    rw [hPsupp, List.range_succ_eq_map, List.map_cons, List.tail_cons, List.map_map]
    rw [List.nodup_map_iff_inj_on List.nodup_range]
    intro a ha b hb hab
    have ha_lt : a < vs.length := List.mem_range.mp ha
    have hb_lt : b < vs.length := List.mem_range.mp hb
    have heq := toF_inj (hbound _ (Nat.mod_lt _ (by omega))) (hbound _ (Nat.mod_lt _ (by omega))) hab
    have hmod_eq := hvs_inj _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega)) heq
    simp only [Nat.succ_eq_add_one] at hmod_eq
    by_cases ha1 : a + 1 < vs.length <;> by_cases hb1 : b + 1 < vs.length
    · rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hb1] at hmod_eq; omega
    · have hb_end : b + 1 = vs.length := by omega
      rw [Nat.mod_eq_of_lt ha1, hb_end, Nat.mod_self] at hmod_eq; omega
    · have ha_end : a + 1 = vs.length := by omega
      rw [ha_end, Nat.mod_self, Nat.mod_eq_of_lt hb1] at hmod_eq; omega
    · omega
  have hPne : P ≠ .nil := by
    intro hnil
    rw [hnil] at hPlen
    simp at hPlen
    omega
  have hedges_nodup : P.edges.Nodup := by
    have hPedges_len : P.edges.length = vs.length := by rw [Walk.length_edges, hPlen]
    let elist := (List.range vs.length).map (fun t =>
      s(Finset.univ.filter (fun b : Fin n => (vs.getD (t % vs.length) 0).testBit b.1),
        Finset.univ.filter (fun b : Fin n => (vs.getD ((t + 1) % vs.length) 0).testBit b.1)))
    have hel_nodup : elist.Nodup := by
      rw [List.nodup_map_iff_inj_on List.nodup_range]
      intro i hi j hj hij
      have hi_lt : i < vs.length := List.mem_range.mp hi
      have hj_lt : j < vs.length := List.mem_range.mp hj
      rw [Sym2.eq_iff] at hij
      rcases hij with ⟨h1, _⟩ | ⟨h1, h2⟩
      · have heq := hvs_inj _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega))
          (toF_inj (hbound _ (Nat.mod_lt _ (by omega))) (hbound _ (Nat.mod_lt _ (by omega))) h1)
        rw [Nat.mod_eq_of_lt hi_lt, Nat.mod_eq_of_lt hj_lt] at heq
        exact heq
      · have heq1 := hvs_inj _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega))
          (toF_inj (hbound _ (Nat.mod_lt _ (by omega))) (hbound _ (Nat.mod_lt _ (by omega))) h1)
        have heq2 := hvs_inj _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega))
          (toF_inj (hbound _ (Nat.mod_lt _ (by omega))) (hbound _ (Nat.mod_lt _ (by omega))) h2)
        rw [Nat.mod_eq_of_lt hi_lt] at heq1
        rw [Nat.mod_eq_of_lt hj_lt] at heq2
        by_cases hi1 : i + 1 < vs.length
        · rw [Nat.mod_eq_of_lt hi1] at heq2
          by_cases hj1 : j + 1 < vs.length
          · rw [Nat.mod_eq_of_lt hj1] at heq1; omega
          · have hj_end : j + 1 = vs.length := by omega
            rw [hj_end, Nat.mod_self] at heq1; omega
        · have hi_end : i + 1 = vs.length := by omega
          rw [hi_end, Nat.mod_self] at heq2
          have hj1 : j + 1 < vs.length := by omega
          rw [Nat.mod_eq_of_lt hj1] at heq1; omega
    have hsub : ∀ e ∈ elist, e ∈ P.edges := by
      intro e he
      rw [List.mem_map] at he
      obtain ⟨t, ht, rfl⟩ := he
      exact hPedges t (List.mem_range.mp ht)
    have hcard_eq : P.edges.toFinset.card = P.edges.length := by
      have h1 : elist.toFinset ⊆ P.edges.toFinset := fun e he =>
        List.mem_toFinset.mpr (hsub e (List.mem_toFinset.mp he))
      have h2 := Finset.card_le_card h1
      rw [List.toFinset_card_of_nodup hel_nodup, List.length_map, List.length_range] at h2
      have h3 := List.toFinset_card_le P.edges
      omega
    have hdedup_len : P.edges.dedup.length = P.edges.length := by
      rw [← List.card_toFinset]; exact hcard_eq
    have hdedup_eq : P.edges.dedup = P.edges :=
      (List.dedup_sublist P.edges).eq_of_length hdedup_len
    rw [← hdedup_eq]
    exact List.nodup_dedup P.edges
  have hPcyc : P.IsCycle := Walk.IsCycle.mk ⟨⟨hedges_nodup⟩, hPne⟩ htail_nodup
  have hPind : P.toSubgraph.IsInduced := by
    intro x hx y hy hadj_xy
    rw [Walk.mem_verts_toSubgraph, hPsupp, List.mem_map] at hx hy
    obtain ⟨ti, _, rfl⟩ := hx
    obtain ⟨tj, _, rfl⟩ := hy
    let i := ti % vs.length
    let j := tj % vs.length
    have hi : i < vs.length := Nat.mod_lt _ (by omega)
    have hj : j < vs.length := Nat.mod_lt _ (by omega)
    have hij : i ≠ j := by
      intro h; exact hadj_xy.ne (by simp [i, j, h])
    have hxor := (toF_adj_iff (hbound i hi) (hbound j hj)).mp hadj_xy
    have hconsec : (i + 1) % vs.length = j ∨ (j + 1) % vs.length = i := by
      by_contra hnot
      push Not at hnot
      exact (hnonadj i hi j hj hij hnot.1 hnot.2).2 hxor
    rw [walk_toSubgraph_adj_iff]
    rcases hconsec with h1 | h2
    · have he := hPedges i hi
      simp only [Nat.mod_eq_of_lt hi, h1] at he
      exact he
    · have he := hPedges j hj
      simp only [Nat.mod_eq_of_lt hj, h2] at he
      rwa [Sym2.eq_swap]
  apply le_csSup (coil_bddAbove n)
  exact ⟨P.toSubgraph, hPind, _, P, hPcyc, rfl, hPlen⟩

private lemma coil_two_ge : 4 ≤ LongestCoilInTheBox 2 :=
  coil_lower_bound_of_list 2 [0, 1, 3, 2] (by decide) (by decide)

private lemma coil_three_ge : 6 ≤ LongestCoilInTheBox 3 :=
  coil_lower_bound_of_list 3 [0, 1, 3, 7, 6, 4] (by decide) (by decide)

private lemma coil_four_ge : 8 ≤ LongestCoilInTheBox 4 :=
  coil_lower_bound_of_list 4 [0, 1, 3, 7, 15, 14, 12, 8] (by decide) (by decide)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private lemma coil_five_ge : 14 ≤ LongestCoilInTheBox 5 :=
  coil_lower_bound_of_list 5 [0, 1, 9, 25, 27, 31, 23, 21, 20, 28, 12, 14, 10, 2]
    (by decide) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private lemma coil_six_ge : 26 ≤ LongestCoilInTheBox 6 :=
  coil_lower_bound_of_list 6
    [0, 1, 9, 13, 45, 37, 36, 52, 20, 28, 24, 56, 57, 49, 51, 35, 43, 42, 46, 62, 63, 31, 23, 7, 6, 2]
    (by decide) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private lemma coil_seven_ge : 48 ≤ LongestCoilInTheBox 7 :=
  coil_lower_bound_of_list 7
    [0, 1, 65, 73, 72, 104, 40, 42, 10, 11, 15, 13, 45, 109, 111, 107, 99, 35, 39, 55, 63, 59, 57,
     25, 24, 28, 60, 124, 126, 122, 90, 91, 95, 93, 85, 117, 113, 112, 48, 50, 18, 22, 86, 70, 102,
     100, 36, 4]
    (by decide) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private lemma coil_eight_ge : 96 ≤ LongestCoilInTheBox 8 :=
  coil_lower_bound_of_list 8
    [0, 32, 33, 35, 39, 47, 46, 42, 58, 56, 57, 61, 53, 52, 54, 22, 86, 84, 85, 93, 89, 88, 72, 74,
     78, 79, 71, 67, 65, 193, 201, 205, 204, 196, 198, 194, 210, 218, 219, 223, 215, 247, 231, 239,
     238, 234, 232, 248, 252, 124, 126, 127, 123, 107, 105, 109, 101, 100, 102, 98, 114, 112, 113,
     241, 177, 176, 178, 162, 166, 164, 172, 173, 169, 171, 187, 191, 190, 158, 142, 138, 136, 152,
     153, 157, 149, 133, 135, 131, 147, 19, 27, 11, 9, 13, 12, 4]
    (by decide) (by decide +kernel)

end Helpers

theorem main : H1 → H2 → H3 → H4 → type_of% @SnakeInBox.coil_small_dimensions := by
  intro h1 h2 h3 h4
  have hc0 : LongestCoilInTheBox 0 = 0 := SnakeInBox.coil_zero_zero
  have hc1 : LongestCoilInTheBox 1 = 0 := coil_one_eq_zero
  have hc2 : LongestCoilInTheBox 2 = 4 := le_antisymm coil_two_le coil_two_ge
  have hc3 : LongestCoilInTheBox 3 = 6 := le_antisymm coil_three_le coil_three_ge
  have hc4 : LongestCoilInTheBox 4 = 8 := le_antisymm coil_four_le coil_four_ge
  have hc5 : LongestCoilInTheBox 5 = 14 := le_antisymm h1 coil_five_ge
  have hc6 : LongestCoilInTheBox 6 = 26 := le_antisymm h2 coil_six_ge
  have hc7 : LongestCoilInTheBox 7 = 48 := le_antisymm h3 coil_seven_ge
  have hc8 : LongestCoilInTheBox 8 = 96 := le_antisymm h4 coil_eight_ge
  show List.map LongestCoilInTheBox (List.range 9) = [0, 0, 4, 6, 8, 14, 26, 48, 96]
  have hr : List.range 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] := by decide
  rw [hr]
  simp only [List.map_cons, List.map_nil, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8]

end OMA.R_SnakeInBox_coil_small_dimensions_R1
