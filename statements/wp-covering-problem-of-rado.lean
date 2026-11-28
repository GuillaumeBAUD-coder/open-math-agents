import Mathlib

/-!
# Radó's covering problem

Among finite families of axis-parallel squares whose union has area one,
determine the sharp guaranteed area of a pairwise disjoint subfamily.

As in Bereg, Dumitrescu, and Jiang, the squares are closed and have positive
side lengths. Two squares that share a boundary point intersect. The greatest
uniform guarantee is the infimum of the best subfamily areas over all such
families.

Source: https://en.wikipedia.org/wiki/Covering_problem_of_Rado
Reference: https://adriandumitrescu.org/rado.pdf
Credit: @konradsiebor
-/

namespace OMA.S_wp_covering_problem_of_rado

abbrev Plane := ℝ × ℝ

structure Square where
  corner : Plane
  side : ℝ
  side_pos : 0 < side

def Square.points (square : Square) : Set Plane :=
  Set.prod
    (Set.Icc square.corner.1 (square.corner.1 + square.side))
    (Set.Icc square.corner.2 (square.corner.2 + square.side))

noncomputable def unionArea (family : Finset Square) : ℝ :=
  (MeasureTheory.volume (⋃ square ∈ family, square.points)).toReal

def GuaranteedArea (area : ℝ) : Prop :=
  ∀ family : Finset Square, unionArea family = 1 →
    ∃ selected : Finset Square, selected ⊆ family ∧
      (selected : Set Square).Pairwise (fun first second =>
        Disjoint first.points second.points) ∧
      area ≤ unionArea selected

theorem main : ∃ area : ℝ, IsGreatest {c : ℝ | GuaranteedArea c} area := by
  sorry

end OMA.S_wp_covering_problem_of_rado
