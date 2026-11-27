import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Harborth's conjecture

Source: https://en.wikipedia.org/wiki/Harborth's_conjecture
Credit: @SubhanAfz
-/

namespace OMA.S_wp_harborth_s_conjecture

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Each edge avoids vertices other than its endpoints, and distinct edges only meet at shared
endpoints. For finite simple graphs, existence of this drawing is equivalent to planarity by
Fáry's theorem. -/
def IsPlaneDrawing {V : Type*} (G : SimpleGraph V) (f : V ↪ Plane) : Prop :=
  (∀ u v, G.Adj u v → ∀ w, w ≠ u → w ≠ v → f w ∉ segment ℝ (f u) (f v)) ∧
  (∀ u v a b, G.Adj u v → G.Adj a b → s(u, v) ≠ s(a, b) →
    segment ℝ (f u) (f v) ∩ segment ℝ (f a) (f b) ⊆ f '' (({u, v} : Set V) ∩ {a, b}))

theorem main :
    ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
      (∃ f : V ↪ Plane, IsPlaneDrawing G f) →
      ∃ f : V ↪ Plane, IsPlaneDrawing G f ∧
        ∀ u v, G.Adj u v → ∃ length : ℕ, dist (f u) (f v) = (length : ℝ) := by
  sorry

end OMA.S_wp_harborth_s_conjecture
