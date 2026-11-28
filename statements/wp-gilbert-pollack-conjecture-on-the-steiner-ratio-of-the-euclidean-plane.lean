import Mathlib

-- Gilbert–Pollak conjecture: the Steiner ratio of the Euclidean plane is √3/2.
-- Source: https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics (Geometry),
-- linking https://en.wikipedia.org/wiki/Steiner_tree_problem#Steiner_ratio
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
Source: the Gilbert–Pollak conjecture states that the Steiner ratio of the Euclidean plane is
`√3/2`. The Steiner tree page phrases the ratio the other way up: the supremum of
(length of minimum spanning tree) / (length of minimum Steiner tree) is conjectured to be
`2/√3`, attained by an equilateral triangle. These are the same statement; here the ratio is
`inf (SMT / MST) = √3/2`.

Conventions:
* The plane is `EuclideanSpace ℝ (Fin 2)`; terminal sets `P` are finite with at least two points
  (so `MST(P) > 0` and the ratio is a genuine quotient).
* `mstLength Q`: the least total Euclidean edge length of a spanning tree on the finite point set
  `Q` (trees on the vertex type `Q`, Mathlib's `SimpleGraph.IsTree`).
* `smtLength P`: the length of a minimum Steiner tree, i.e. the infimum of `mstLength Q` over
  finite `Q ⊇ P`: a Steiner tree is a tree whose vertices are the terminals plus extra (Steiner)
  points joined by straight segments, and for a fixed vertex set the shortest such tree is a
  minimum spanning tree.
* All infima are of nonempty sets of nonnegative reals, so `sInf` is a genuine infimum.
-/

namespace OMA.S_wp_gilbert_pollack_conjecture_on_the_steiner_ratio_of_the_euclidean_plane

/-- Euclidean length of an edge between two points of `Q`. -/
noncomputable def edgeLength (Q : Finset (EuclideanSpace ℝ (Fin 2))) : Sym2 Q → ℝ :=
  Sym2.lift ⟨fun a b => dist (a : EuclideanSpace ℝ (Fin 2)) b, fun a b => dist_comm _ _⟩

open Classical in
/-- Length of a minimum spanning tree on the finite point set `Q`. -/
noncomputable def mstLength (Q : Finset (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  sInf {L : ℝ | ∃ T : SimpleGraph Q, T.IsTree ∧ L = ∑ e ∈ T.edgeFinset, edgeLength Q e}

/-- Length of a minimum Steiner tree for the terminal set `P`. -/
noncomputable def smtLength (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  sInf {L : ℝ | ∃ Q : Finset (EuclideanSpace ℝ (Fin 2)), P ⊆ Q ∧ L = mstLength Q}

/-- The Gilbert–Pollak conjecture: the Steiner ratio of the Euclidean plane is `√3/2`. -/
theorem main : sInf {r : ℝ | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), 2 ≤ P.card ∧
    r = smtLength P / mstLength P} = Real.sqrt 3 / 2 := by
  sorry

end OMA.S_wp_gilbert_pollack_conjecture_on_the_steiner_ratio_of_the_euclidean_plane
