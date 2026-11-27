import Mathlib

/-!
# Double-critical graph conjecture

Source: https://www.openproblemgarden.org/op/double_critical_graph_conjecture
Credit: @lzvxck

The source (Erdős–Lovász): a connected simple graph `G` is called double-critical if removing
any pair of adjacent vertices lowers the chromatic number by two. Conjecture: `K_n` is the
only `n`-chromatic double-critical graph.

Graphs are finite. Removing the adjacent vertices `u, v` gives the induced subgraph on the
other vertices. "`G` is `K_n`" for an `n`-chromatic `G` means `G` is complete (then `n` is its
number of vertices), so the conclusion is `G = ⊤`.
-/

namespace OMA.S_opg_double_critical_graph_conjecture

/-- `G` is double-critical: connected, and deleting any two adjacent vertices lowers the
chromatic number by exactly two. -/
def IsDoubleCritical {V : Type*} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ u v, G.Adj u v →
    (G.induce ({u, v}ᶜ : Set V)).chromaticNumber = G.chromaticNumber - 2

/-- **Double-critical graph conjecture.** The only finite double-critical graphs are the
complete graphs. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsDoubleCritical G → G = ⊤ := by
  sorry

end OMA.S_opg_double_critical_graph_conjecture
