import Mathlib

/-!
# Cycle double cover conjecture

Source: https://en.wikipedia.org/wiki/cycle_double_cover_conjecture
Credit: @joshuadc11

Every finite bridgeless graph has a family (multiset) of cycles that includes each edge
of the graph exactly twice.

Formalization notes:
- A graph `G : SimpleGraph V` is bridgeless iff `∀ e : Sym2 V, ¬ G.IsBridge e`.
- A finite multiset of cycles is represented as an indexed family `c : ∀ i : Fin k, G.Walk (v i) (v i)`
  with `(c i).IsCycle` for every `i` (cycles may repeat at distinct indices `i`).
- Since every cycle has duplicate-free edge list, each edge `e ∈ G.edgeSet` is included exactly
  twice iff `(Finset.univ.filter (fun i : Fin k => e ∈ (c i).edges)).card = 2`.
-/

namespace OMA.S_wp_cycle_double_cover_conjecture

theorem main :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ e : Sym2 V, ¬ G.IsBridge e) →
      ∃ (k : ℕ) (v : Fin k → V) (c : ∀ i : Fin k, G.Walk (v i) (v i)),
        (∀ i, (c i).IsCycle) ∧
        ∀ e ∈ G.edgeSet, (Finset.univ.filter (fun i : Fin k => e ∈ (c i).edges)).card = 2 := by
  sorry

end OMA.S_wp_cycle_double_cover_conjecture
