import Mathlib

/-!
# Decomposing an even tournament in directed paths

Source: https://www.openproblemgarden.org/op/decomposing_an_even_tournament_in_directed_paths
Credit: @ishaanzee

**Conjecture** (B. Alspach, D. W. Mason, N. J. Pullman). Every tournament `D` on an even number of vertices can be decomposed into
`∑_{v ∈ V} max{0, d⁺(v) - d⁻(v)}` directed paths.

(This is tight: in any decomposition at least `max{0, d⁺(v) - d⁻(v)}` paths start at `v`. The
analogue fails for odd tournaments, e.g. regular ones.)

Formalization:
* A tournament on a finite set `V` is a relation `T` with no loops and exactly one of `T u v`,
  `T v u` for distinct `u`, `v`; `d⁺(v)` and `d⁻(v)` are the numbers of out- and in-neighbours.
  In `ℕ`, `d⁺(v) - d⁻(v)` is already truncated at `0`, i.e. it equals `max{0, d⁺(v) - d⁻(v)}`.
* A directed path is a list of distinct vertices with at least one arc, each vertex having an arc
  to the next one; its arcs are the pairs of consecutive vertices.
* A decomposition into directed paths is a list of such paths in which every arc of the tournament
  occurs exactly once among all the paths' arcs.
-/

namespace OMA.S_opg_decomposing_an_even_tournament_in_directed_paths

/-- The arcs of a path given as a list of vertices: its consecutive pairs. -/
def pathArcs {V : Type*} (p : List V) : List (V × V) := p.zip p.tail

/-- **Conjecture**: every tournament with an even number of vertices decomposes into exactly
`∑_v max{0, d⁺(v) - d⁻(v)}` directed paths. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T],
    (∀ v, ¬ T v v) → (∀ u v, u ≠ v → (T u v ↔ ¬ T v u)) → Even (Fintype.card V) →
      ∃ P : List (List V),
        (∀ p ∈ P, p.Nodup ∧ 2 ≤ p.length ∧ ∀ a ∈ pathArcs p, T a.1 a.2) ∧
        (P.flatMap pathArcs).Nodup ∧
        (∀ u v : V, T u v ↔ (u, v) ∈ P.flatMap pathArcs) ∧
        P.length = ∑ v : V, ((Finset.univ.filter fun w => T v w).card -
          (Finset.univ.filter fun w => T w v).card) := by
  sorry

end OMA.S_opg_decomposing_an_even_tournament_in_directed_paths
