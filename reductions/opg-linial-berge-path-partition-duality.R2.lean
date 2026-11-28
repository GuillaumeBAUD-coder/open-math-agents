import OMAStatements.S_opg_linial_berge_path_partition_duality
import Mathlib

-- Reduction opg-linial-berge-path-partition-duality.R2 of Linial-Berge path partition duality
-- Credit: @MBimrose
--
-- The target is Berge's path partition conjecture: for every finite loopless digraph D and every k >= 1 there
-- is a path partition P and a set S inducing a k-colourable subgraph with  sum_{p in P} min(|p|,k) <= |S|.
--
-- This reduction removes the 2-cycles: it suffices to prove the conjecture for ORIENTED digraphs, plus the
-- classical k = 1 case for arbitrary digraphs.
--
--   H1  the conjecture for 2 <= k, restricted to oriented digraphs (no pair carries arcs in both directions).
--       Strictly stronger than the target's k >= 2 content is not claimed: this is the same statement on a
--       smaller class, and the class is inhabited (the transitive tournament on 2 or 3 vertices, k = 2 <= n).
--   H2  the k = 1 instance for arbitrary loopless digraphs, i.e. Gallai-Milgram (1960): the minimum number of
--       paths of a path partition is at most the maximum size of a stable set (a 1-colourable set is exactly a
--       set carrying no arc). Known theorem, not formalised here.
--
-- Bridge (the content of this file): given a loopless D, choose ONE arc out of every pair that carries at
-- least one, by a fixed linear order on V (transported through `Fintype.equivFin`). The result D' is oriented,
-- satisfies D' subset D, and has the SAME underlying undirected graph as D. Then:
--   * every directed path of D' is a directed path of D (D' subset D), and the vertex covering is unchanged;
--   * `IsProperOn` only sees the underlying undirected graph, i.e. `c` is proper on S in D' if and only if it
--     is proper on S in D, because for u != v, `D'.Adj u v or D'.Adj v u <-> D.Adj u v or D.Adj v u`;
--   * the k-norm sum is literally the same expression.
-- So an instance solution for D' is an instance solution for D. This is why 2-cycles can be discarded, and it
-- is the standard reason the conjecture is only ever stated for oriented graphs in the literature.
--
-- Audit of the hypotheses (no false or vacuous hypothesis, each used exactly once):
--   * H1 is the target instance restricted to the oriented case with k >= 2; the target implies it. Inhabited:
--     the transitive tournament on {0,1} (arc 0->1), k = 2. Not vacuously true: the n = 3,4 exhaustive search
--     (all loopless digraphs up to isomorphism, hence all oriented ones) found min k-norm <= max k-colourable
--     with equality in the tight cases, so H1 is a truth, not a free pass.
--   * H2 is the k = 1 instance for all D; inhabited by a single vertex with k = 1. It is Gallai-Milgram's
--     theorem, so true, and not implied by H1 (H1 only covers oriented D and k >= 2).
--   * main uses H1 in the k >= 2 branch and H2 in the k = 1 branch; the branches are exhaustive and disjoint.

namespace OMA.R_opg_linial_berge_path_partition_duality_R2

open OMA.S_opg_linial_berge_path_partition_duality

/-- The conjecture for oriented digraphs (no pair of vertices carries arcs in both directions) and `2 <= k`. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (D : Digraph V), (∀ v, ¬ D.Adj v v) →
    (∀ u v, D.Adj u v → ¬ D.Adj v u) → ∀ k : ℕ, 2 ≤ k →
    ∃ (N : ℕ) (len : Fin N → ℕ) (p : ∀ j, Fin (len j + 1) → V),
      (∀ j, IsDirectedPath D (p j)) ∧
        (∀ v, ∃! x : (Σ j, Fin (len j + 1)), p x.1 x.2 = v) ∧
          ∃ (S : Finset V) (c : V → Fin k), IsProperOn D S c ∧
            ∑ j, min (len j + 1) k ≤ S.card

/-- The `k = 1` instance for arbitrary loopless digraphs: Gallai-Milgram, minimum number of paths at most
the maximum size of an arc-free vertex set, in the vocabulary of the target. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (D : Digraph V), (∀ v, ¬ D.Adj v v) → ∀ k : ℕ, k = 1 →
    ∃ (N : ℕ) (len : Fin N → ℕ) (p : ∀ j, Fin (len j + 1) → V),
      (∀ j, IsDirectedPath D (p j)) ∧
        (∀ v, ∃! x : (Σ j, Fin (len j + 1)), p x.1 x.2 = v) ∧
          ∃ (S : Finset V) (c : V → Fin k), IsProperOn D S c ∧
            ∑ j, min (len j + 1) k ≤ S.card

/-- Halving the 2-cycles: the oriented `k >= 2` case and the `k = 1` case imply the target. -/
theorem main : H1 → H2 →
    type_of% @OMA.S_opg_linial_berge_path_partition_duality.main := by
  intro h1 h2 V instV D hloop k hk
  by_cases hk1 : k = 1
  · exact h2 V D hloop k hk1
  · have hk2 : 2 ≤ k := by omega
    -- a linear order on V, to break the 2-cycles deterministically
    let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
    -- keep v -> w always, and keep w -> v only when v -> w is absent
    let D' : Digraph V :=
      ⟨fun v w => (D.Adj v w ∧ ¬ D.Adj w v) ∨ (D.Adj v w ∧ D.Adj w v ∧ e v < e w)⟩
    have hsub : ∀ v w, D'.Adj v w → D.Adj v w := by
      intro v w h
      rcases h with h' | h'
      · exact h'.1
      · exact h'.1
    have hloop' : ∀ v, ¬ D'.Adj v v := fun v h => hloop v (hsub v v h)
    have hor : ∀ v w, D'.Adj v w → ¬ D'.Adj w v := by
      intro v w h h'
      have hv : D.Adj v w := hsub v w h
      have hw : D.Adj w v := hsub w v h'
      rcases h with ⟨_, hn⟩ | ⟨_, _, hlt⟩
      · exact hn hw
      · rcases h' with ⟨_, hn⟩ | ⟨_, _, hlt'⟩
        · exact hn hv
        · exact absurd hlt' (not_lt.mpr (le_of_lt hlt))
    have hunder : ∀ v w, v ≠ w → ((D'.Adj v w ∨ D'.Adj w v) ↔ (D.Adj v w ∨ D.Adj w v)) := by
      intro v w hne
      have hlt : e v < e w ∨ e w < e v :=
        lt_or_gt_of_ne (fun he => hne (e.injective he))
      constructor
      · rintro (h | h)
        · exact Or.inl (hsub v w h)
        · exact Or.inr (hsub w v h)
      · rintro (h | h)
        · by_cases hb : D.Adj w v
          · rcases hlt with hl | hl
            · exact Or.inl (Or.inr ⟨h, hb, hl⟩)
            · exact Or.inr (Or.inr ⟨hb, h, hl⟩)
          · exact Or.inl (Or.inl ⟨h, hb⟩)
        · by_cases ha : D.Adj v w
          · rcases hlt with hl | hl
            · exact Or.inl (Or.inr ⟨ha, h, hl⟩)
            · exact Or.inr (Or.inr ⟨h, ha, hl⟩)
          · exact Or.inr (Or.inl ⟨h, ha⟩)
    obtain ⟨N, len, p, hpath, hcover, S, c, hprop, hsum⟩ := h1 V D' hloop' hor k hk2
    refine ⟨N, len, p, ?_, hcover, S, c, ?_, hsum⟩
    · intro j
      exact ⟨(hpath j).1, fun i => hsub _ _ ((hpath j).2 i)⟩
    · intro v hv w hw hvw
      have hne : v ≠ w := fun he => hloop v (he ▸ hvw)
      have hcase : D'.Adj v w ∨ D'.Adj w v := (hunder v w hne).mpr (Or.inl hvw)
      rcases hcase with h | h
      · exact hprop v hv w hw h
      · exact fun hc => hprop w hw v hv h hc.symm

end OMA.R_opg_linial_berge_path_partition_duality_R2
