import OMAStatements.S_opg_non_edges_vs_feedback_edge_sets_in_digraphs
import Mathlib.Tactic

-- Reduction opg-non-edges-vs-feedback-edge-sets-in-digraphs.R1 of Non-edges vs. feedback edge sets in digraphs
-- (Chudnovsky-Seymour-Sullivan conjecture; Open Problem Garden op/non_edges_vs_feedback_edge_sets_in_digraphs).
--
-- Notation below: n = |V|, m = #arcs = #{p : V x V // G.Adj p.1 p.2}, and
-- `orderedNonEdges G` = 2 * gamma(G) (ordered pairs of distinct non-adjacent vertices).
-- The target is: if G has no directed cycle of length <= 3 then beta(G) <= gamma(G)/2,
-- i.e. some feedback arc set F has 4 * |F| <= orderedNonEdges G.
--
-- PROVED IN `main` HERE (unconditionally, no hypothesis on G beyond the target's own premise):
--   the conjecture holds whenever  6 * m <= n * (n - 1).
--   Reason: `counting` below proves the exact count  n*(n-1) <= orderedNonEdges G + 2*m
--   (each of the n(n-1) ordered pairs of distinct vertices is an arc, the reverse of an arc, or a
--   non-edge), so with F = the set of ALL arcs (which trivially leaves no arc, hence no cycle)
--   we get 4*m <= orderedNonEdges G.  Equivalently: the conjecture holds whenever
--   gamma(G) >= n(n-1)/3 = (2/3) * binom(n,2).
--
-- THE HARD CONTENT IS ISOLATED in H1: the same statement for the complementary DENSE region
--   4 * m > n * (n - 1)   (equivalently gamma(G) < n(n-1)/4),
-- which is exactly the region of the known extremal examples (the whole conjecture is sharp at the
-- directed 4-cycle: n = 4, m = 4, gamma = 2, beta = 1); the OPG circulants C_{3k+1}(1..k) are dense too.
--
-- H2 is NOT open: it is the elementary averaging fact that every digraph has a feedback arc set of
-- size at most m/2 (fix any linear order of V; the "backward" arcs and the "forward" arcs are each
-- feedback arc sets -- deleting either leaves only arcs increasing along the order -- and they
-- partition the arc set, so one of them has at most m/2 arcs). It is isolated because in this file
-- its use already covers the whole middle region n(n-1)/6 < m <= n(n-1)/4 for free: together with
-- the unconditional part, `main` + H2 covers gamma(G) >= n(n-1)/4. Formalising H2 (a vertex
-- ordering, the partition of the arcs into forward/backward, and "increasing arcs are acyclic")
-- would remove it from the hypotheses; nothing else about the conjecture is hidden in it.
--
-- So the only remaining case is H1, the dense case, and that is the conjecture itself.

namespace OMA.R_opg_non_edges_vs_feedback_edge_sets_in_digraphs_R1
open OMA.S_opg_non_edges_vs_feedback_edge_sets_in_digraphs

/-- The hard case: the conjecture for digraphs with `4*m > n*(n-1)` (`m` = number of arcs).
Equivalently `gamma(G) < n(n-1)/4`. This is where every sharp example lives. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
    (∀ (m : ℕ) (c : Fin m → V), m ≤ 3 → ¬ IsDirectedCycle G c) →
    4 * (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2)).card >
        Fintype.card V * (Fintype.card V - 1) →
    ∃ F : Finset (V × V), (∀ p ∈ F, G.Adj p.1 p.2) ∧
      (∀ (m : ℕ) (c : Fin m → V), ¬ IsDirectedCycle (deleteArcs G F) c) ∧
      4 * F.card ≤ orderedNonEdges G

/-- Every digraph (no hypothesis at all) has a feedback arc set of at most half its arcs. Elementary:
take any linear order of `V`; the arcs that go backwards in that order form a feedback arc set, and so
do the arcs that go forwards (they partition the arc set), hence the smaller of the two works. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
    ∃ F : Finset (V × V), (∀ p ∈ F, G.Adj p.1 p.2) ∧
      (∀ (m : ℕ) (c : Fin m → V), ¬ IsDirectedCycle (deleteArcs G F) c) ∧
      2 * F.card ≤ (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2)).card

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

/-- Bridge: the sparse/tight part of the conjecture is proved outright, the middle part comes from
H2 (at most half the arcs), and the dense part is H1. -/
theorem main : H1 → H2 → type_of% @OMA.S_opg_non_edges_vs_feedback_edge_sets_in_digraphs.main := by
  intro h1 h2 V _ _ G _ hcyc
  set B : Finset (V × V) := Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2) with hB
  have hcount := counting G
  rw [← hB] at hcount
  by_cases hdense : Fintype.card V * (Fintype.card V - 1) < 4 * B.card
  · exact h1 V G hcyc hdense
  · push_neg at hdense
    by_cases hthin : 6 * B.card ≤ Fintype.card V * (Fintype.card V - 1)
    · -- F = every arc: the digraph left over has no arc at all, and the count above gives the inequality
      refine ⟨B, ?_, ?_, ?_⟩
      · intro p hp
        rw [hB] at hp
        simpa using hp
      · rintro m c hc
        simp only [IsDirectedCycle] at hc
        obtain ⟨hm, -, harc⟩ := hc
        have h0 : (deleteArcs G B).Adj (c ⟨0, hm⟩) (c (finRotate m ⟨0, hm⟩)) :=
          harc ⟨0, hm⟩
        obtain ⟨hadj, hnot⟩ := h0
        exact hnot (by rw [hB]; simpa using hadj)
      · omega
    · -- middle region: half the arcs suffice
      push_neg at hthin
      obtain ⟨F, hF1, hF2, hF3⟩ := h2 V G
      have hF3' : 2 * F.card ≤ B.card := by rw [hB]; exact hF3
      refine ⟨F, hF1, hF2, ?_⟩
      omega

end OMA.R_opg_non_edges_vs_feedback_edge_sets_in_digraphs_R1
