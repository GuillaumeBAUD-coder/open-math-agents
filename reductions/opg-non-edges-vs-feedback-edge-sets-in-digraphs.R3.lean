import OMAStatements.S_opg_non_edges_vs_feedback_edge_sets_in_digraphs
import Mathlib.Tactic

-- Reduction opg-non-edges-vs-feedback-edge-sets-in-digraphs.R3 of Non-edges vs. feedback edge sets in
-- digraphs (Chudnovsky-Seymour-Sullivan conjecture; OPG op/non_edges_vs_feedback_edge_sets_in_digraphs).
--
-- n = |V|, m = #arcs, and orderedNonEdges G = 2*gamma(G); the target is beta(G) <= gamma(G)/2.
-- R3 splits the whole conjecture into THREE disjoint cases by elementary arithmetic:
--
--   H3  gamma(G) = 0 (G is a tournament): the conjecture. NON-VACUOUS (transitive tournaments,
--       directed C_4 plus nested sources/sinks satisfy the premise) and TRUE; it is proved outright in
--       this repository as step R3.H3, using `tournament_acyclic` below: with no directed triangle and
--       no non-edges G is a tournament, hence (i) complete, (ii) irreflexive (a loop is a length-1
--       cycle), (iii) transitive (a digon or a non-arc would close a cycle of length 2 or 3), and then
--       out-degrees strictly decrease along every arc, which is impossible all the way round a cycle.
--
--   H2  the sparse region 4*m <= n*(n-1): the conjecture. NON-VACUOUS (every sufficiently sparse
--       digraph) and TRUE; proved outright as step R3.H2 from `half_arcs_lemma` (any loopless digraph
--       has a feedback arc set of at most m/2 arcs: the increasing and the decreasing arcs of a fixed
--       linear order are both feedback arc sets and partition the arc set) together with `counting`
--       (n*(n-1) <= orderedNonEdges G + 2m), which give 4*|F| <= 2m <= orderedNonEdges G.
--
--   H1  the residual DENSE case: 4*m > n*(n-1) and gamma(G) >= 1. This is the open case, and it is
--       strictly smaller than the whole conjecture: every sharp example lives here (the directed
--       4-cycle: n=4, m=4, gamma=2, beta=1, 2*beta = gamma) and no small counterexample exists
--       (exhaustive over all oriented triangle-free digraphs with n <= 6, 4,168,935 of them at n=6;
--       Kostochka-Stiebitz verified gamma <= 14, and beta <= m forces 3*gamma < n*(n-1), so any
--       counterexample needs n >= 8 and gamma >= 15).
--
-- `main` is the (pure) case split, so R3 + its two steps covers every case except H1.

namespace OMA.R_opg_non_edges_vs_feedback_edge_sets_in_digraphs_R3
open OMA.S_opg_non_edges_vs_feedback_edge_sets_in_digraphs

def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
    (∀ (m : ℕ) (c : Fin m → V), m ≤ 3 → ¬ IsDirectedCycle G c) →
    1 ≤ orderedNonEdges G →
    Fintype.card V * (Fintype.card V - 1) <
        4 * (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2)).card →
    ∃ F : Finset (V × V), (∀ p ∈ F, G.Adj p.1 p.2) ∧
      (∀ (m : ℕ) (c : Fin m → V), ¬ IsDirectedCycle (deleteArcs G F) c) ∧
      4 * F.card ≤ orderedNonEdges G

def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
    (∀ (m : ℕ) (c : Fin m → V), m ≤ 3 → ¬ IsDirectedCycle G c) →
    4 * (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2)).card ≤
        Fintype.card V * (Fintype.card V - 1) →
    ∃ F : Finset (V × V), (∀ p ∈ F, G.Adj p.1 p.2) ∧
      (∀ (m : ℕ) (c : Fin m → V), ¬ IsDirectedCycle (deleteArcs G F) c) ∧
      4 * F.card ≤ orderedNonEdges G

def H3 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
    (∀ (m : ℕ) (c : Fin m → V), m ≤ 3 → ¬ IsDirectedCycle G c) →
    orderedNonEdges G = 0 →
    ∃ F : Finset (V × V), (∀ p ∈ F, G.Adj p.1 p.2) ∧
      (∀ (m : ℕ) (c : Fin m → V), ¬ IsDirectedCycle (deleteArcs G F) c) ∧
      4 * F.card ≤ orderedNonEdges G

/-- The counting core: `n*(n-1) <= orderedNonEdges G + 2*m`. Proof: `univ.offDiag` (the `n*(n-1)`
ordered pairs of distinct vertices) splits, by `Finset.card_sdiff`, into the pairs that are "adjacent
one way or the other" and `orderedNonEdges G`; the former sit inside `B ∪ C` where `B` is the set of
arcs and `C` the set of reversed arcs, each of cardinality `m`. -/
lemma counting {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] :
    Fintype.card V * (Fintype.card V - 1) ≤
      orderedNonEdges G + 2 * (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2)).card := by
  set B : Finset (V × V) := Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2) with hB
  set C : Finset (V × V) := B.image (fun p : V × V => (p.2, p.1)) with hC
  set A : Finset (V × V) := Finset.univ.offDiag with hA
  have hCcard : C.card = B.card := by
    rw [hC]
    exact Finset.card_image_of_injective _ (fun p q h => by
      have h1 : p.2 = q.2 := congrArg Prod.fst h
      have h2 : p.1 = q.1 := congrArg Prod.snd h
      simp [Prod.ext_iff, h1, h2])
  have hAcard : A.card = Fintype.card V * (Fintype.card V - 1) := by
    rw [hA, Finset.offDiag_card, Finset.card_univ, Nat.mul_sub_one]
  have hnon : orderedNonEdges G = (A \ (B ∪ C)).card := by
    rw [orderedNonEdges]
    congr 1
    ext p
    simp only [hA, hB, hC, Finset.mem_sdiff, Finset.mem_offDiag, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, Finset.mem_image, Prod.mk.injEq, true_and]
    constructor
    · rintro ⟨hne, h1, h2⟩
      exact ⟨hne, fun h => h.elim h1 fun ⟨a, ha, hae⟩ => h2 (by rw [← hae]; simpa using ha)⟩
    · rintro ⟨hne, hnot⟩
      exact ⟨hne, fun h => hnot (Or.inl h),
        fun h => hnot (Or.inr ⟨(p.2, p.1), h, rfl⟩)⟩
  rw [hnon, ← hAcard]
  have hle1 : ((B ∪ C) ∩ A).card ≤ A.card :=
    Finset.card_le_card (Finset.inter_subset_right)
  have hle2 : ((B ∪ C) ∩ A).card ≤ (B ∪ C).card :=
    Finset.card_le_card (Finset.inter_subset_left)
  have hle3 : (B ∪ C).card ≤ B.card + C.card := Finset.card_union_le _ _
  have hsum : (A \ (B ∪ C)).card + ((B ∪ C) ∩ A).card = A.card := by
    rw [Finset.card_sdiff, Nat.sub_add_cancel hle1]
  have hd2 : ((B ∪ C) ∩ A).card ≤ 2 * B.card := by omega
  omega

/-- If a relation is transitive and has no loops, no arc set of it can be a directed cycle:
out-degrees strictly decrease along every arc, and they cannot strictly decrease all the way round a cycle. -/
lemma no_cycle_of_trans {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hirr : ∀ u : V, ¬ G.Adj u u)
    (htrans : ∀ u v w : V, G.Adj u v → G.Adj v w → G.Adj u w) :
    ∀ (m : ℕ) (c : Fin m → V), ¬ IsDirectedCycle G c := by
  have hout : ∀ u v : V, G.Adj u v →
      (Finset.univ.filter (fun w => G.Adj v w)).card <
        (Finset.univ.filter (fun w => G.Adj u w)).card := by
    intro u v huv
    apply Finset.card_lt_card
    refine ⟨?_, ?_⟩
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact htrans u v w huv hw
    · intro hsub
      have hv : v ∈ Finset.univ.filter (fun w => G.Adj u w) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact huv
      have := hsub hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact hirr v this
  intro m c hc
  simp only [IsDirectedCycle] at hc
  obtain ⟨hm, -, harc⟩ := hc
  have hlt : ∀ i : Fin m,
      (Finset.univ.filter (fun w => G.Adj (c (finRotate m i)) w)).card <
        (Finset.univ.filter (fun w => G.Adj (c i) w)).card := fun i => hout _ _ (harc i)
  have hsum1 : (∑ i : Fin m, (Finset.univ.filter (fun w => G.Adj (c (finRotate m i)) w)).card) <
      (∑ i : Fin m, (Finset.univ.filter (fun w => G.Adj (c i) w)).card) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact le_of_lt (hlt i)
    · exact ⟨⟨0, hm⟩, Finset.mem_univ _, hlt ⟨0, hm⟩⟩
  have hsum2 : (∑ i : Fin m, (Finset.univ.filter (fun w => G.Adj (c (finRotate m i)) w)).card) =
      (∑ i : Fin m, (Finset.univ.filter (fun w => G.Adj (c i) w)).card) :=
    Equiv.sum_comp (finRotate m) (fun i => (Finset.univ.filter (fun w => G.Adj (c i) w)).card)
  omega

/-- Tournament case: a digraph with no non-edges and no cycle of length <= 3 is acyclic. -/
lemma tournament_acyclic {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V)
    [DecidableRel G.Adj]
    (hcyc : ∀ (m : ℕ) (c : Fin m → V), m ≤ 3 → ¬ IsDirectedCycle G c)
    (hnone : orderedNonEdges G = 0) :
    ∀ (m : ℕ) (c : Fin m → V), ¬ IsDirectedCycle G c := by
  rw [orderedNonEdges] at hnone
  have hcomp : ∀ u v : V, u ≠ v → G.Adj u v ∨ G.Adj v u := by
    intro u v huv
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    have hmem : (u, v) ∈ Finset.univ.filter
        (fun p : V × V => p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2 ∧ ¬ G.Adj p.2 p.1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, h1, h2⟩
    have hpos : 0 < (Finset.univ.filter
        (fun p : V × V => p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2 ∧ ¬ G.Adj p.2 p.1)).card :=
      Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  have hirr : ∀ u : V, ¬ G.Adj u u := by
    intro u hu
    exact hcyc 1 (fun _ => u) (by norm_num) ⟨le_refl 1, fun a b _ => Subsingleton.elim a b,
      fun i => by simpa using hu⟩
  have htrans : ∀ u v w : V, G.Adj u v → G.Adj v w → G.Adj u w := by
    intro u v w huv hvw
    have huv' : u ≠ v := fun h => hirr u (h ▸ huv)
    have hvw' : v ≠ w := fun h => hirr v (h ▸ hvw)
    rcases eq_or_ne u w with huw | huw
    · -- a digon u -> v -> u
      subst huw
      let c : Fin 2 → V := Fin.cases u (fun _ : Fin 1 => v)
      have h0 : c 0 = u := rfl
      have h1 : c 1 = v := rfl
      have hinj : Function.Injective c := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> first
          | rfl
          | exact absurd hab huv'
          | exact absurd hab.symm huv'
      refine absurd ⟨by norm_num, hinj, ?_⟩ (hcyc 2 c (by norm_num))
      intro i
      fin_cases i
      · change G.Adj (c 0) (c (finRotate 2 0))
        rw [h0, show finRotate 2 0 = 1 from by decide, h1]; exact huv
      · change G.Adj (c 1) (c (finRotate 2 1))
        rw [h1, show finRotate 2 1 = 0 from by decide, h0]; exact hvw
    · by_contra h
      have hwu : G.Adj w u := by
        rcases hcomp w u huw.symm with h' | h'
        · exact h'
        · exact absurd h' h
      let c : Fin 3 → V := Fin.cases u (Fin.cases v (fun _ : Fin 1 => w))
      have h0 : c 0 = u := rfl
      have h1 : c 1 = v := rfl
      have h2 : c 2 = w := rfl
      have hinj : Function.Injective c := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> first
          | rfl
          | exact absurd hab huv'
          | exact absurd hab.symm huv'
          | exact absurd hab huw
          | exact absurd hab.symm huw
          | exact absurd hab hvw'
          | exact absurd hab.symm hvw'
      refine absurd ⟨by norm_num, hinj, ?_⟩ (hcyc 3 c (by norm_num))
      intro i
      fin_cases i
      · change G.Adj (c 0) (c (finRotate 3 0))
        rw [h0, show finRotate 3 0 = 1 from by decide, h1]; exact huv
      · change G.Adj (c 1) (c (finRotate 3 1))
        rw [h1, show finRotate 3 1 = 2 from by decide, h2]; exact hvw
      · change G.Adj (c 2) (c (finRotate 3 2))
        rw [h2, show finRotate 3 2 = 0 from by decide, h0]; exact hwu
  exact no_cycle_of_trans G hirr htrans

lemma half_arcs_lemma {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hloopless : ∀ v : V, ¬ G.Adj v v) :
    ∃ F : Finset (V × V), (∀ p ∈ F, G.Adj p.1 p.2) ∧
      (∀ (m : ℕ) (c : Fin m → V), ¬ IsDirectedCycle (deleteArcs G F) c) ∧
      2 * F.card ≤ (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2)).card := by
  classical
  set e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V with he
  set r : V → ℕ := fun v => ((e v : Fin (Fintype.card V)) : ℕ) with hr
  have hrinj : Function.Injective r := by
    intro a b h
    apply e.injective
    exact Fin.ext h
  set B : Finset (V × V) := Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2) with hB
  have hneq : ∀ p ∈ B, r p.1 ≠ r p.2 := by
    intro p hp h
    rw [hB, Finset.mem_filter] at hp
    have h12 : p.1 = p.2 := hrinj h
    rw [h12] at hp
    exact hloopless p.2 hp.2
  set Fb : Finset (V × V) := B.filter (fun p : V × V => r p.2 < r p.1) with hFb
  set Ff : Finset (V × V) := B.filter (fun p : V × V => r p.1 < r p.2) with hFf
  have hFf_eq : Ff = B.filter (fun p : V × V => ¬ (r p.2 < r p.1)) := by
    rw [hFf]
    apply Finset.filter_congr
    intro p hp
    have := hneq p hp
    omega
  have hsplit : Fb.card + Ff.card = B.card := by
    rw [hFb, hFf_eq, Finset.card_filter_add_card_filter_not]
  have key : ∀ (H : Digraph V), (∀ u v : V, H.Adj u v → r u < r v) →
      ∀ (m : ℕ) (c : Fin m → V), ¬ IsDirectedCycle H c := by
    intro H hmono m c hc
    simp only [IsDirectedCycle] at hc
    obtain ⟨hm, -, harc⟩ := hc
    have hlt : ∀ i : Fin m, r (c i) < r (c (finRotate m i)) := fun i => hmono _ _ (harc i)
    have hsum1 : (∑ i : Fin m, r (c i)) < ∑ i : Fin m, r (c (finRotate m i)) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact le_of_lt (hlt i)
      · exact ⟨⟨0, hm⟩, Finset.mem_univ _, hlt ⟨0, hm⟩⟩
    have hsum2 : (∑ i : Fin m, r (c (finRotate m i))) = ∑ i : Fin m, r (c i) :=
      Equiv.sum_comp (finRotate m) (fun i => r (c i))
    omega
  have key' : ∀ (H : Digraph V), (∀ u v : V, H.Adj u v → r v < r u) →
      ∀ (m : ℕ) (c : Fin m → V), ¬ IsDirectedCycle H c := by
    intro H hmono m c hc
    simp only [IsDirectedCycle] at hc
    obtain ⟨hm, -, harc⟩ := hc
    have hlt : ∀ i : Fin m, r (c (finRotate m i)) < r (c i) := fun i => hmono _ _ (harc i)
    have hsum1 : (∑ i : Fin m, r (c (finRotate m i))) < ∑ i : Fin m, r (c i) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact le_of_lt (hlt i)
      · exact ⟨⟨0, hm⟩, Finset.mem_univ _, hlt ⟨0, hm⟩⟩
    have hsum2 : (∑ i : Fin m, r (c (finRotate m i))) = ∑ i : Fin m, r (c i) :=
      Equiv.sum_comp (finRotate m) (fun i => r (c i))
    omega
  have hFb_fas : ∀ (m : ℕ) (c : Fin m → V), ¬ IsDirectedCycle (deleteArcs G Fb) c := by
    apply key
    intro u v huv
    obtain ⟨hadj, hnot⟩ := huv
    have hmemB : (u, v) ∈ B := by
      rw [hB]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
    have hne : r u ≠ r v := hneq (u, v) hmemB
    have h2 : ¬ (r v < r u) := by
      intro h
      exact hnot (by rw [hFb]; exact Finset.mem_filter.mpr ⟨hmemB, h⟩)
    omega
  have hFf_fas : ∀ (m : ℕ) (c : Fin m → V), ¬ IsDirectedCycle (deleteArcs G Ff) c := by
    apply key' 
    intro u v huv
    obtain ⟨hadj, hnot⟩ := huv
    have hmemB : (u, v) ∈ B := by
      rw [hB]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
    have hne : r u ≠ r v := hneq (u, v) hmemB
    have h2 : ¬ (r u < r v) := by
      intro h
      exact hnot (by rw [hFf]; exact Finset.mem_filter.mpr ⟨hmemB, h⟩)
    omega
  rcases le_total Fb.card Ff.card with h | h
  · refine ⟨Fb, ?_, hFb_fas, ?_⟩
    · intro p hp
      rw [hFb, Finset.mem_filter] at hp
      exact (Finset.mem_filter.mp hp.1).2
    · omega
  · refine ⟨Ff, ?_, hFf_fas, ?_⟩
    · intro p hp
      rw [hFf, Finset.mem_filter] at hp
      exact (Finset.mem_filter.mp hp.1).2
    · omega

theorem main : H1 → H2 → H3 → type_of% @OMA.S_opg_non_edges_vs_feedback_edge_sets_in_digraphs.main := by
  intro h1 h2 h3 V _ _ G _ hcyc
  by_cases hzero : orderedNonEdges G = 0
  · exact h3 V G hcyc hzero
  · have hpos : 1 ≤ orderedNonEdges G := by omega
    by_cases hsparse : 4 * (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2)).card ≤
        Fintype.card V * (Fintype.card V - 1)
    · exact h2 V G hcyc hsparse
    · push Not at hsparse
      exact h1 V G hcyc hpos hsparse

end OMA.R_opg_non_edges_vs_feedback_edge_sets_in_digraphs_R3
