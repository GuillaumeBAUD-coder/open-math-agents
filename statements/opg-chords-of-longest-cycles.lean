import Mathlib

/-!
# Chords of longest cycles

Source: https://www.openproblemgarden.org/op/chords_of_longest_cycles
Credit: @lzvxck

Thomassen's conjecture, as stated in the source: if `G` is a 3-connected graph, every longest
cycle in `G` has a chord. A chord of a cycle `C` is an edge `e` so that `e ∉ E(C)`, but both
ends of `e` are in `V(C)`.

Conventions: graphs are finite and simple. `G` is `k`-connected if it has more than `k`
vertices and stays connected after deleting any set of fewer than `k` vertices. A longest
cycle is a cycle of `G` whose length is at least the length of every cycle of `G`.
-/

namespace OMA.S_opg_chords_of_longest_cycles

/-- `G` is `k`-connected: more than `k` vertices, and deleting fewer than `k` vertices leaves
a connected graph. -/
def IsKConnected {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Connected

/-- `c` is a longest cycle of `G`: a cycle at least as long as every cycle of `G`. -/
def IsLongestCycle {V : Type*} (G : SimpleGraph V) {v : V} (c : G.Walk v v) : Prop :=
  c.IsCycle ∧ ∀ (w : V) (d : G.Walk w w), d.IsCycle → d.length ≤ c.length

/-- The cycle `c` has a chord: an edge of `G` not on `c` with both ends on `c`. -/
def HasChord {V : Type*} (G : SimpleGraph V) {v : V} (c : G.Walk v v) : Prop :=
  ∃ x y : V, G.Adj x y ∧ s(x, y) ∉ c.edges ∧ x ∈ c.support ∧ y ∈ c.support

/-- **Chords of longest cycles (Thomassen).** In a 3-connected graph every longest cycle has
a chord. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsKConnected G 3 →
    ∀ (v : V) (c : G.Walk v v), IsLongestCycle G c → HasChord G c := by
  sorry

end OMA.S_opg_chords_of_longest_cycles
