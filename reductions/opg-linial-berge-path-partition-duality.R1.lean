import OMAStatements.S_opg_linial_berge_path_partition_duality
import Mathlib

-- Reduction opg-linial-berge-path-partition-duality.R1 of Linial-Berge path partition duality
-- Credit: @MBimrose
--
-- The target (Berge's path partition conjecture) asks, for every finite loopless digraph D and every k >= 1,
-- for a path partition P and a set S inducing a k-colourable subgraph with
--     sum over the paths of min(|P|, k)  <=  |S| .
-- This split is a case analysis on (k, D), into four classes that are handled by four statements of
-- different mathematical nature. The bridge `main` is pure dispatch; the content of the conjecture lives
-- in the hypotheses, one per class:
--
--   H1  k = 1 : this is exactly the Gallai-Milgram theorem (1960): the minimum number of paths in a path
--       partition is at most the maximum size of a stable set. k-norm of a path partition with k = 1 is
--       the number of paths, and a 1-colourable S is a stable set (an arc inside S would need two
--       different colours). Known theorem, not formalised here.
--   H2  the genuinely open core: 2 <= k < |V| and D has NO directed Hamiltonian path. Everything that is
--       not H2 is reducible: with a Hamiltonian path the instance is tight at k (see H3), and for
--       k >= |V| it is free (see H4).
--   H3  D has a directed Hamiltonian path and 2 <= k < |V|. Provable: one path covering D has k-norm
--       min(|V|, k) = k, and the first k vertices of that path are k-colourable by an injective
--       colouring (k vertices, k colours). Stated as a hypothesis so that the case split is explicit;
--       it is a self-contained, provable step (proofs/<id>.R1.H3.lean).
--   H4  k >= |V|. Provable: the partition into singletons has k-norm |V|, and S = V is k-colourable
--       by an injective map V -> Fin k since |V| <= k. Self-contained, provable step
--       (proofs/<id>.R1.H4.lean).
--
-- Audit of the hypotheses (no false or vacuous hypothesis, each is used):
--   * H1's domain is nonempty (D = single vertex, k = 1) and H1 is a known theorem.
--   * H2's domain is nonempty: D = three vertices with one arc 0 -> 1 has no Hamiltonian path and
--     2 <= k < 3 holds for k = 2; D = two isolated vertices, k = 2 as well.
--   * H3's domain is nonempty: the directed path on three vertices, k = 2; the directed 3-cycle, k = 2.
--   * H4's domain is nonempty: the single vertex with k = 1; the empty two-vertex digraph with k = 2.
--   * Each hypothesis is the target instance restricted to its class, so each is implied by the target;
--     none is stronger than the target, and none is vacuously true for every digraph (each class is
--     inhabited by the witnesses above).
--   * main uses each of H1..H4 in exactly one branch of an exhaustive, mutually exclusive case split.

namespace OMA.R_opg_linial_berge_path_partition_duality_R1

open OMA.S_opg_linial_berge_path_partition_duality

/-- `k = 1`: the Gallai-Milgram case. A path partition whose 1-norm (its number of paths) is at most the
size of a stable set, in the vocabulary of the target. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (D : Digraph V), (∀ v, ¬ D.Adj v v) → ∀ k : ℕ, k = 1 →
    ∃ (N : ℕ) (len : Fin N → ℕ) (p : ∀ j, Fin (len j + 1) → V),
      (∀ j, IsDirectedPath D (p j)) ∧
        (∀ v, ∃! x : (Σ j, Fin (len j + 1)), p x.1 x.2 = v) ∧
          ∃ (S : Finset V) (c : V → Fin k), IsProperOn D S c ∧
            ∑ j, min (len j + 1) k ≤ S.card

/-- The open core: `2 <= k < |V|` and no directed Hamiltonian path. This is the only part of the
conjecture that is not settled by the construction of a Hamiltonian path or by `k >= |V|`. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (D : Digraph V), (∀ v, ¬ D.Adj v v) → ∀ k : ℕ, 2 ≤ k → k < Fintype.card V →
    (¬ ∃ (l : ℕ) (q : Fin (l + 1) → V), IsDirectedPath D q ∧ l + 1 = Fintype.card V) →
    ∃ (N : ℕ) (len : Fin N → ℕ) (p : ∀ j, Fin (len j + 1) → V),
      (∀ j, IsDirectedPath D (p j)) ∧
        (∀ v, ∃! x : (Σ j, Fin (len j + 1)), p x.1 x.2 = v) ∧
          ∃ (S : Finset V) (c : V → Fin k), IsProperOn D S c ∧
            ∑ j, min (len j + 1) k ≤ S.card

/-- `2 <= k < |V|` with a directed Hamiltonian path: one path through D has k-norm `k`, and its first
`k` vertices can be coloured injectively, so the class is provable. -/
def H3 : Prop :=
  ∀ (V : Type) [Fintype V] (D : Digraph V), (∀ v, ¬ D.Adj v v) → ∀ k : ℕ, 2 ≤ k → k < Fintype.card V →
    (∃ (l : ℕ) (q : Fin (l + 1) → V), IsDirectedPath D q ∧ l + 1 = Fintype.card V) →
    ∃ (N : ℕ) (len : Fin N → ℕ) (p : ∀ j, Fin (len j + 1) → V),
      (∀ j, IsDirectedPath D (p j)) ∧
        (∀ v, ∃! x : (Σ j, Fin (len j + 1)), p x.1 x.2 = v) ∧
          ∃ (S : Finset V) (c : V → Fin k), IsProperOn D S c ∧
            ∑ j, min (len j + 1) k ≤ S.card

/-- `k >= |V|`: the free case. `S = V` with an injective colouring and the partition into singletons
have k-norm `|V|`, so the class is provable. -/
def H4 : Prop :=
  ∀ (V : Type) [Fintype V] (D : Digraph V), (∀ v, ¬ D.Adj v v) → ∀ k : ℕ, Fintype.card V ≤ k →
    ∃ (N : ℕ) (len : Fin N → ℕ) (p : ∀ j, Fin (len j + 1) → V),
      (∀ j, IsDirectedPath D (p j)) ∧
        (∀ v, ∃! x : (Σ j, Fin (len j + 1)), p x.1 x.2 = v) ∧
          ∃ (S : Finset V) (c : V → Fin k), IsProperOn D S c ∧
            ∑ j, min (len j + 1) k ≤ S.card

/-- The four classes cover every instance, so the four statements imply the target. -/
theorem main : H1 → H2 → H3 → H4 →
    type_of% @OMA.S_opg_linial_berge_path_partition_duality.main := by
  intro h1 h2 h3 h4 V instV D hloop k hk
  by_cases hk1 : k = 1
  · exact h1 V D hloop k hk1
  · by_cases hbig : Fintype.card V ≤ k
    · exact h4 V D hloop k hbig
    · have hlt : k < Fintype.card V := not_le.mp hbig
      have hk2 : 2 ≤ k := by omega
      by_cases hham : ∃ (l : ℕ) (q : Fin (l + 1) → V), IsDirectedPath D q ∧ l + 1 = Fintype.card V
      · exact h3 V D hloop k hk2 hlt hham
      · exact h2 V D hloop k hk2 hlt hham

end OMA.R_opg_linial_berge_path_partition_duality_R1
