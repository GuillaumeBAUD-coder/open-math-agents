import Mathlib

/-!
# Obstacle number of planar graphs

Source: https://www.openproblemgarden.org/op/obstacle_number_of_planar_graphs
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (Alpert, Koch, Laison): is there some `k` such that every planar graph has obstacle
number at most `k`? `main` states the positive answer; a proof of its negation answers no.
(The page's first question, whether some planar graph has obstacle number greater than `1`, is
not the statement here.)

Conventions:
* Graphs are finite simple graphs.
* A `k`-obstacle drawing maps the vertices injectively to points of the plane and has `k`
  polygonal obstacles avoiding those points, such that two distinct vertices are adjacent iff the
  segment joining their points meets no obstacle. A polygonal obstacle is a closed region bounded
  by a simple polygon: a finite union of closed triangles that is homeomorphic to a closed disc.
* Planar: a crossing-free straight-line drawing exists (equivalent to planarity by Fáry's
  theorem): vertex points are distinct, no vertex point lies on the segment of an edge not at that
  vertex, and the segments of two edges meet only in a common endpoint.
-/

namespace OMA.S_opg_obstacle_number_of_planar_graphs

/-- The plane. -/
abbrev P := EuclideanSpace ℝ (Fin 2)

/-- A polygonal obstacle: a finite union of closed triangles homeomorphic to a closed disc. -/
def IsPolygonalObstacle (S : Set P) : Prop :=
  (∃ T : Finset (Fin 3 → P), S = ⋃ t ∈ T, convexHull ℝ (Set.range t)) ∧
    Nonempty (S ≃ₜ Metric.closedBall (0 : P) 1)

/-- `G` has an obstacle drawing with at most `k` obstacles. -/
def HasObstacleDrawing {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (pos : V → P) (obs : List (Set P)), Function.Injective pos ∧ obs.length ≤ k ∧
    (∀ O ∈ obs, IsPolygonalObstacle O ∧ ∀ v, pos v ∉ O) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ ∀ O ∈ obs, Disjoint (segment ℝ (pos u) (pos v)) O)

/-- `G` has a crossing-free straight-line drawing. -/
def IsPlanar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ pos : V → P, Function.Injective pos ∧
    (∀ u v w, G.Adj u v → w ≠ u → w ≠ v → pos w ∉ segment ℝ (pos u) (pos v)) ∧
    ∀ u v u' v', G.Adj u v → G.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ x ∈ segment ℝ (pos u) (pos v), x ∈ segment ℝ (pos u') (pos v') →
        (x = pos u ∨ x = pos v) ∧ (x = pos u' ∨ x = pos v')

theorem main :
    ∃ k : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsPlanar G → HasObstacleDrawing G k := by
  sorry

end OMA.S_opg_obstacle_number_of_planar_graphs
