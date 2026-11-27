import Mathlib

/-!
# Chords of longest cycles

Source: https://www.openproblemgarden.org/op/chords_of_longest_cycles
Conjecture of Thomassen: if `G` is a 3-connected graph, then every longest cycle of `G` has a
chord. A chord of a cycle `C` is an edge `e` with `e` not an edge of `C` but both ends of `e`
vertices of `C`.

Mathlib has neither vertex connectivity nor the circumference of a graph, so both notions are
defined here in the standard way: 3-connected means at least four vertices and connected after
deleting any set of at most two vertices; longest means that no cycle of `G` is longer.
-/

namespace OMA.S_opg_chords_of_longest_cycles

/-- A graph is 3-connected when it has at least four vertices and remains connected after the
deletion of any set of at most two vertices. -/
def IsThreeConnected {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧ ∀ S : Finset V, S.card ≤ 2 → (G.induce {v : V | v ∉ S}).Connected

/-- An edge of `G` joining two vertices of the closed walk `C` which is not an edge of `C`: a
chord of the cycle `C`. -/
def HasChord {V : Type*} (G : SimpleGraph V) {a : V} (C : G.Walk a a) : Prop :=
  ∃ u v : V, u ∈ C.support ∧ v ∈ C.support ∧ G.Adj u v ∧ s(u, v) ∉ C.edges

/-- Thomassen's conjecture: every longest cycle of a 3-connected graph has a chord. -/
theorem main : ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsThreeConnected G → ∀ {a : V} (C : G.Walk a a), C.IsCycle →
      (∀ ⦃b : V⦄ (C' : G.Walk b b), C'.IsCycle → C'.length ≤ C.length) → HasChord G C := by
  sorry

end OMA.S_opg_chords_of_longest_cycles
