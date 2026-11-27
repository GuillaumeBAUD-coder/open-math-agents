import Mathlib

/-!
# Linial–Berge path partition duality

Source: https://www.openproblemgarden.org/op/linial_berge_path_partition_duality
Credit: @ishaanzee

**Conjecture** (C. Berge, N. Linial). The minimum `k`-norm of a path partition on a directed graph
`D` is no more than the maximal size of an induced `k`-colorable subgraph.

Definitions: a path partition of `D` is a set of vertex-disjoint (directed) paths in it (some might
be singletons) covering all vertices. For a positive integer `k`, the `k`-norm of a path partition
is the sum of `min{|V(P)|, k}` over all paths `P` in it.

Formalization:
* A directed graph on a finite set `V` is a loopless relation `D` (`D u v` is the arc `u → v`);
  colorings refer to its underlying undirected graph (`SimpleGraph.fromRel D`).
* A directed path is a nonempty list of distinct vertices with an arc from each vertex to the next.
  A path partition is a list of directed paths whose concatenation contains every vertex exactly
  once.
* "Minimum `k`-norm ≤ maximum size of an induced `k`-colorable subgraph" is equivalent to: some path
  partition has `k`-norm at most `|S|` for some vertex set `S` inducing a `k`-colorable subgraph.
-/

namespace OMA.S_opg_linial_berge_path_partition_duality

/-- `P` is a path partition of the digraph `D`. -/
def IsPathPartition {V : Type*} (D : V → V → Prop) (P : List (List V)) : Prop :=
  (∀ p ∈ P, p ≠ [] ∧ p.Nodup ∧ ∀ a ∈ p.zip p.tail, D a.1 a.2) ∧
    P.flatten.Nodup ∧ ∀ v : V, v ∈ P.flatten

/-- The `k`-norm of a path partition. -/
def kNorm {V : Type*} (k : ℕ) (P : List (List V)) : ℕ := (P.map fun p => min p.length k).sum

/-- **Berge–Linial path partition conjecture.** -/
theorem main : ∀ (k : ℕ) (V : Type) [Fintype V] (D : V → V → Prop), 1 ≤ k → (∀ v, ¬ D v v) →
    ∃ P : List (List V), IsPathPartition D P ∧
      ∃ S : Set V, ((SimpleGraph.fromRel D).induce S).Colorable k ∧ kNorm k P ≤ S.ncard := by
  sorry

end OMA.S_opg_linial_berge_path_partition_duality
