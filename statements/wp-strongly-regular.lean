import Mathlib

/-!
# Strongly regular geodetic graphs

Source: https://en.wikipedia.org/wiki/Strongly_regular_graph
Credit: @ihateSAS

Open problem: do there exist infinitely many strongly regular geodetic graphs,
or any strongly regular geodetic graphs that are not Moore graphs?

A graph is geodetic when any two vertices are joined by exactly one shortest path.
In the strongly regular setting a Moore graph is a strongly regular graph with
`λ = 0` and `μ = 1` (girth five, diameter two); that is the reading used below.
-/

namespace OMA.S_wp_strongly_regular

/-- A graph is geodetic if any two vertices are joined by exactly one shortest path. -/
def IsGeodetic {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃! p : G.Walk u v, p.IsPath ∧ p.length = G.dist u v

/-- A strongly regular geodetic graph: geodetic, and strongly regular for some parameters. -/
def IsStronglyRegularGeodetic {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  letI := Classical.decRel G.Adj
  ∃ n k l μ : ℕ, G.IsSRGWith n k l μ ∧ IsGeodetic G

/-- A Moore graph, read as a strongly regular graph with `λ = 0` and `μ = 1`. -/
def IsMooreGraph {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  letI := Classical.decRel G.Adj
  ∃ n k : ℕ, G.IsSRGWith n k 0 1

theorem main :
    (Set.Infinite {n : ℕ | ∃ G : SimpleGraph (Fin n), IsStronglyRegularGeodetic G}) ∨
      (∃ (n : ℕ) (G : SimpleGraph (Fin n)),
        IsStronglyRegularGeodetic G ∧ ¬ IsMooreGraph G) := by
  sorry

end OMA.S_wp_strongly_regular
