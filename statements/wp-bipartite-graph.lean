import Mathlib

/-!
# Do crown graphs require the longest word-representants among bipartite graphs?

Source: https://en.wikipedia.org/wiki/Bipartite_graph (open problem listed with the article; see also
https://en.wikipedia.org/wiki/Word-representable_graph, Open problems, and M. Glen, S. Kitaev,
A. Pyatkin, On the representation number of a crown graph, Discrete Appl. Math. 244 (2018))
Credit: @sntntHb

The source asks: is it true that out of all bipartite graphs, crown graphs require longest
word-representants?

Definitions from the source (Word-representable graph): letters `a` and `b` alternate in a word `w`
if, after removing from `w` all letters but the copies of `a` and `b`, one obtains `abab...` or
`baba...`. A graph `G = (V, E)` is word-representable if there is a word `w` over the alphabet `V`
such that `a` and `b` alternate in `w` iff `ab` is an edge. A graph is `k`-representable if it is
represented by a word having exactly `k` copies of each letter; the representation number of `G` is
the minimum such `k` (it is `∞` for a graph that is not word-representable). The crown graph
`H_{n,n}` is the complete bipartite graph `K_{n,n}` with the edges of a perfect matching removed.

## Encoding

* `Alternate w a b`: the subword of `w` consisting of the copies of `a` and `b` has no two equal
  adjacent letters (that is, it reads `abab...` or `baba...`).
* `IsRepresentedBy G k w`: every vertex occurs exactly `k` times in `w`, and for distinct `a`, `b`,
  `a` and `b` alternate in `w` iff `G.Adj a b`.
* `representationNumber G : ℕ∞` is the least `k ≥ 1` with such a word (`⊤` if there is none).
  Since all representing words of one graph with `k` copies of each letter have the same length
  `k * |V|`, longer word-representants means a larger representation number among graphs with the
  same number of vertices.
* A bipartite graph is a graph with a proper `2`-colouring (`G.Colorable 2`).
* Crown graphs have an even number `2n` of vertices; the proposition formalized is that every
  bipartite graph on `2n` vertices has representation number at most that of the crown graph
  `H_{n,n}` on `2n` vertices, for every `n`.
-/

namespace OMA.S_wp_bipartite_graph

variable {V : Type} [DecidableEq V]

/-- Letters `a` and `b` alternate in `w`: deleting all other letters leaves `abab...` or `baba...`. -/
def Alternate (w : List V) (a b : V) : Prop :=
  List.IsChain (· ≠ ·) (w.filter (fun x => decide (x = a ∨ x = b)))

/-- The word `w` has exactly `k` copies of each letter and represents `G`. -/
def IsRepresentedBy (G : SimpleGraph V) (k : ℕ) (w : List V) : Prop :=
  (∀ v : V, w.count v = k) ∧ ∀ a b : V, a ≠ b → (G.Adj a b ↔ Alternate w a b)

/-- The representation number of `G` (`⊤` if `G` is not word-representable). -/
noncomputable def representationNumber (G : SimpleGraph V) : ℕ∞ :=
  sInf {r : ℕ∞ | ∃ k : ℕ, 0 < k ∧ r = k ∧ ∃ w : List V, IsRepresentedBy G k w}

/-- The crown graph `H_{n,n}`: `K_{n,n}` on `Fin n ⊕ Fin n` minus the perfect matching
`{inl i, inr i}` (`inl i` and `inr j` are adjacent iff `i ≠ j`; no other edges). -/
def crownGraph (n : ℕ) : SimpleGraph (Fin n ⊕ Fin n) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | Sum.inl i, Sum.inr j => i ≠ j
    | _, _ => False

/-- **Open problem.** Among bipartite graphs, crown graphs require the longest word-representants:
every bipartite graph on `2n` vertices has representation number at most that of `H_{n,n}`. -/
theorem main : ∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W], Fintype.card W = 2 * n →
    ∀ G : SimpleGraph W, G.Colorable 2 →
      representationNumber G ≤ representationNumber (crownGraph n) := by
  sorry

end OMA.S_wp_bipartite_graph
