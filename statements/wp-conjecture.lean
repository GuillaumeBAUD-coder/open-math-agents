import Mathlib

/-!
# The γ–θ question for eternal domination

Source: https://en.wikipedia.org/wiki/Eternal_dominating_set#Open_questions
Credit: @sntntHb

The source (Wikipedia, Eternal dominating set) defines the eternal domination game: mobile guards
start on a dominating set of a graph `G`, at most one guard per vertex. An infinite sequence of
attacks at vertices follows; an attack at a vertex with no guard on it must be defended by moving a
guard from an adjacent vertex onto the attacked vertex, and the configuration must stay dominating.
The eternal domination number `γ∞(G)` is the minimum number of guards that can defend every
sequence of attacks. It satisfies `γ(G) ≤ γ∞(G) ≤ θ(G)` (`θ` the clique covering number), and the
open question in the source is:

  Does there exist a graph `G` such that `γ(G) = γ∞(G)` and `γ(G)` is less than the clique
  covering number of `G`?

## Encoding

* Graphs are finite simple graphs `SimpleGraph V` with `[Fintype V]`.
* `γ(G)` is the least size of a dominating set (every vertex is in `D` or adjacent to a vertex of `D`).
* A guard configuration is a `Finset V` (at most one guard per vertex). `k` guards can defend every
  attack sequence forever iff there is a nonempty family `F` of `k`-element dominating
  configurations such that for every `D ∈ F` and every unguarded vertex `v`, some guard `u ∈ D`
  adjacent to `v` can move to `v` with the new configuration `insert v (D.erase u)` again in `F`
  (the winning region of this finite safety game). `γ∞(G)` is the least such `k`.
* `θ(G)` is the least number of cliques partitioning `V`: the least `k` with a map `f : V → Fin k`
  whose fibres are cliques (equivalently the chromatic number of the complement, as the source notes).

The theorem states that such a graph exists (the proposition asked about in the source).
-/

namespace OMA.S_wp_conjecture

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `D` is a dominating set of `G`. -/
def IsDominating (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v : V, v ∈ D ∨ ∃ u ∈ D, G.Adj u v

/-- The domination number `γ(G)`. -/
noncomputable def dominationNumber (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ D : Finset V, D.card = k ∧ IsDominating G D}

/-- `F` is a family of `k`-guard configurations from which every attack can be defended forever:
each configuration is dominating, and every attack at an unguarded vertex `v` can be answered by
moving one guard from a neighbour of `v` onto `v`, reaching again a configuration of `F`. -/
def IsEternalFamily (G : SimpleGraph V) (k : ℕ) (F : Set (Finset V)) : Prop :=
  F.Nonempty ∧ (∀ D ∈ F, D.card = k ∧ IsDominating G D) ∧
    ∀ D ∈ F, ∀ v : V, v ∉ D → ∃ u ∈ D, G.Adj u v ∧ insert v (D.erase u) ∈ F

/-- The eternal domination number `γ∞(G)`. -/
noncomputable def eternalDominationNumber (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ F : Set (Finset V), IsEternalFamily G k F}

/-- The clique covering number `θ(G)`: the least number of cliques partitioning the vertices. -/
noncomputable def cliqueCoverNumber (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ f : V → Fin k, ∀ u v : V, u ≠ v → f u = f v → G.Adj u v}

/-- **The γ–θ question.** There is a finite graph `G` with `γ(G) = γ∞(G)` and `γ(G) < θ(G)`. -/
theorem main : ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
    dominationNumber G = eternalDominationNumber G ∧ dominationNumber G < cliqueCoverNumber G := by
  sorry

end OMA.S_wp_conjecture
