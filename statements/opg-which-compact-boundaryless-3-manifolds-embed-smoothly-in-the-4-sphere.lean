import Mathlib

namespace OMA.S_opg_which_compact_boundaryless_3_manifolds_embed_smoothly_in_the_4_sphere

open Manifold
open scoped BigOperators ContDiff Manifold

abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev Sphere (d : ℕ) := ↥(Metric.sphere (0 : Euclidean (d + 1)) 1)

abbrev TriangulationCode := ℕ × List (List ℕ)

/-- Glue the listed abstract simplices by common faces using barycentric coordinates. -/
abbrev Realization (code : TriangulationCode) :=
  {x : Fin code.1 → ℝ // (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧
    ∃ simplex ∈ code.2, ∀ i, x i ≠ 0 → i.val ∈ simplex}

def vertexLink (code : TriangulationCode) (v : ℕ) : TriangulationCode :=
  (code.1, (code.2.filter (fun tetra => decide (v ∈ tetra))).map (fun tetra => tetra.erase v))

/-- A finite pure tetrahedral complex with all vertex links two-spheres.
An unused label is not a vertex of the generated complex. -/
def IsClosedThreeManifoldCode (code : TriangulationCode) : Prop :=
  (∀ tetra ∈ code.2, tetra.length = 4 ∧ tetra.Nodup ∧ ∀ v ∈ tetra, v < code.1) ∧
  ∀ v : ℕ, (∃ tetra ∈ code.2, v ∈ tetra) →
    Nonempty (Realization (vertexLink code v) ≃ₜ Sphere 2)

/-- The standard smooth four-sphere is the target. In dimension three, the
smooth structure of a triangulated manifold is unique up to diffeomorphism. -/
def EmbedsSmoothly (code : TriangulationCode) : Prop :=
  ∃ atlas : ChartedSpace (Euclidean 3) (Realization code),
    letI := atlas
    ∃ smooth : IsManifold (𝓡 3) ∞ (Realization code),
      letI := smooth
      ∃ f : Realization code → Sphere 4, IsSmoothEmbedding (𝓡 3) (𝓡 4) ∞ f

/-- Is smooth embeddability of a compact boundaryless 3-manifold in the
standard 4-sphere decidable from a finite triangulation? -/
theorem main :
    ∃ test : TriangulationCode → Prop, ComputablePred test ∧
      ∀ code : TriangulationCode, IsClosedThreeManifoldCode code →
        (test code ↔ EmbedsSmoothly code) := by
  sorry

end OMA.S_opg_which_compact_boundaryless_3_manifolds_embed_smoothly_in_the_4_sphere
