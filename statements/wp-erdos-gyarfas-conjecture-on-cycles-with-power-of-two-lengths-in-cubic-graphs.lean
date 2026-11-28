import Mathlib

/-!
# Erdős–Gyárfás conjecture

Source: https://en.wikipedia.org/wiki/Erdős–Gyárfás_conjecture
Credit: @joshuadc11

Every finite nonempty simple graph with minimum degree at least `3` contains a simple cycle
whose length is a power of two.

Formalization notes:
- Minimum degree at least `3` is `∀ v : V, 3 ≤ G.degree v` (with `[Nonempty V]` so the graph
  has at least one vertex).
- A simple cycle of length `2 ^ k` is a walk `p : G.Walk v v` with `p.IsCycle` and
  `p.length = 2 ^ k` (since simple-graph cycles have length `≥ 3`, this automatically forces `k ≥ 2`).
-/

namespace OMA.S_wp_erdos_gyarfas_conjecture_on_cycles_with_power_of_two_lengths_in_cubic_graphs

theorem main :
    ∀ (V : Type*) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v : V, 3 ≤ G.degree v) →
      ∃ (v : V) (p : G.Walk v v) (k : ℕ), p.IsCycle ∧ p.length = 2 ^ k := by
  sorry

end OMA.S_wp_erdos_gyarfas_conjecture_on_cycles_with_power_of_two_lengths_in_cubic_graphs
