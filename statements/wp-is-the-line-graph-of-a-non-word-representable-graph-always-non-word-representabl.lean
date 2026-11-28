import Mathlib

/-!
# Is the line graph of a non-word-representable graph always non-word-representable?

Source: https://en.wikipedia.org/wiki/line_graph
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

Word-representability (standard definition, Kinnersley; cf. Wikipedia "Word-representable graph"):
a graph $G$ on vertex set $V$ is word-representable if there is a word $w$ over $V$ in which every
vertex occurs, such that for all $u, v$: $u$ and $v$ are adjacent in $G$ iff $u$ and $v$ alternate
in $w$ — i.e. the subword of $w$ restricted to $u, v$ is $(uv)^k$ or $(vu)^k$ for some $k \ge 1$.
The question: is the line graph of every non-word-representable graph again non-word-representable?
-/

namespace OMA.S_wp_is_the_line_graph_of_a_non_word_representable_graph_always_non_word_representabl

/-- The subword of `w` restricted to the letters `x` and `y`. -/
noncomputable def restrict (w : List α) (x y : α) : List α := by
  classical
  induction w with
  | nil => exact []
  | cons z w ih => exact (if z = x ∨ z = y then z :: ih else ih)

/--
`Alternates w x y`: the letters `x ≠ y` alternate in the word `w` — the subword of `w`
restricted to `x` and `y` is `(xy)^k` or `(yx)^k` for some `k ≥ 1`.
-/
def Alternates (w : List α) (x y : α) : Prop :=
  x ≠ y ∧ ∃ k ≥ 1,
    restrict w x y = List.flatten (List.replicate k [x, y]) ∨
      restrict w x y = List.flatten (List.replicate k [y, x])

/--
`IsWordRepresentable G`: there is a word over `V` in which every vertex occurs, such that two
vertices are adjacent in `G` exactly when they alternate in the word.
-/
def IsWordRepresentable {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ w : List V, (∀ v : V, v ∈ w) ∧ ∀ u v, G.Adj u v ↔ Alternates w u v

/--
The question: if `G` is not word-representable, must its line graph also fail to be
word-representable?
-/
theorem main :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet],
      ¬ IsWordRepresentable G → ¬ IsWordRepresentable (SimpleGraph.lineGraph G) := by
  sorry

end OMA.S_wp_is_the_line_graph_of_a_non_word_representable_graph_always_non_word_representabl
