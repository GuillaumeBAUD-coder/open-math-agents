import Mathlib

/-!
# Dense rational distance sets in the plane

Source: https://www.openproblemgarden.org/op/dense_rational_distance_sets_in_the_plane
Credit: @joshuadc11

Erdős–Ulam problem: does there exist a dense set `S ⊆ ℝ²` such that all pairwise Euclidean
distances between points in `S` are rational?

## Encoding

* `ℝ²` with the Euclidean metric is `EuclideanSpace ℝ (Fin 2)` (not `ℝ × ℝ`, which carries the
  sup-norm metric in Mathlib).
* Dense is Mathlib's `Dense S`.
* All pairwise distances are rational: `∀ x ∈ S, ∀ y ∈ S, ∃ q : ℚ, dist x y = (q : ℝ)`.
* The source notes that Ulam guessed the answer is negative; `main` states the conjectured negative
  answer (so a disproof would exhibit such a dense rational-distance set).
-/

namespace OMA.S_opg_dense_rational_distance_sets_in_the_plane

/-- There is no dense subset of the Euclidean plane `ℝ²` in which all pairwise distances are
rational. -/
theorem main : ¬ ∃ S : Set (EuclideanSpace ℝ (Fin 2)),
    Dense S ∧ ∀ x ∈ S, ∀ y ∈ S, ∃ q : ℚ, dist x y = (q : ℝ) := by
  sorry

end OMA.S_opg_dense_rational_distance_sets_in_the_plane
