import Mathlib

/-!
# 4-regular 4-chromatic graphs of high girth

Source: https://www.openproblemgarden.org/op/high_girth_low_degree_4_chromatic_graphs
Credit: @ishaanzee

**Problem** (B. Grünbaum). Do there exist 4-regular 4-chromatic graphs of arbitrarily high girth?

Grünbaum conjectured that for every `m` there are `m`-regular `m`-chromatic graphs of
arbitrarily high girth; Johansson's theorem (`χ ≤ C Δ / log Δ` for triangle-free graphs) shows
this is false for large `m`, but the case `m = 4` is open. We state the affirmative answer.

Formalization: graphs are finite simple graphs. For every `g` there is a finite graph that is
4-regular (`IsRegularOfDegree 4`), has chromatic number exactly `4` (`chromaticNumber`, valued in
`ℕ∞`), and has girth at least `g`. We use `egirth` (the length of a shortest cycle, `⊤` for an
acyclic graph); a finite 4-regular graph is never acyclic, so this is the usual girth.
-/

namespace OMA.S_opg_high_girth_low_degree_4_chromatic_graphs

/-- **Grünbaum's question**, affirmative form: there are finite 4-regular 4-chromatic graphs of
arbitrarily large girth. -/
theorem main : ∀ g : ℕ, ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    G.IsRegularOfDegree 4 ∧ G.chromaticNumber = 4 ∧ (g : ℕ∞) ≤ G.egirth := by
  sorry

end OMA.S_opg_high_girth_low_degree_4_chromatic_graphs
