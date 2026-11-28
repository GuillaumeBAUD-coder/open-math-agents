import Mathlib

/-!
# Kalai's 3^d conjecture

Source: https://en.wikipedia.org/wiki/Kalai's_3^d_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Kalai, 1989): every centrally symmetric `d`-dimensional polytope has at least `3^d`
nonempty faces (counting the polytope itself as a face).

Conventions:
* A `d`-dimensional polytope is the convex hull of a finite set `S ⊆ ℝ^d` whose affine span is
  all of `ℝ^d`; it is centrally symmetric if it equals its own image under `x ↦ -x` (every
  centrally symmetric polytope is a translate of one symmetric about the origin, and face
  counts are translation invariant).
* The faces of a polytope are exactly its exposed faces (`IsExposed`), which include the
  polytope itself; we count the nonempty ones.
-/

namespace OMA.S_wp_kalai_s_3d_conjecture

/-- The number of nonempty faces of a set `P ⊆ ℝ^d`. -/
noncomputable def faceCount {d : ℕ} (P : Set (EuclideanSpace ℝ (Fin d))) : ℕ :=
  {F : Set (EuclideanSpace ℝ (Fin d)) | IsExposed ℝ P F ∧ F.Nonempty}.ncard

/-- Kalai's `3^d` conjecture. -/
theorem main : ∀ (d : ℕ) (S : Finset (EuclideanSpace ℝ (Fin d))),
    affineSpan ℝ (S : Set (EuclideanSpace ℝ (Fin d))) = ⊤ →
    (∀ x ∈ convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin d))),
      -x ∈ convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin d)))) →
    3 ^ d ≤ faceCount (convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin d)))) := by
  sorry

end OMA.S_wp_kalai_s_3d_conjecture
