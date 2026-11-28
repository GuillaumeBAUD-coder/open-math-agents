import Mathlib

/-!
# Generalised Empty Hexagon Conjecture

Source: https://www.openproblemgarden.org/op/generalised_empty_hexagon_conjecture
Credit: @sun-jiao

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_opg_generalised_empty_hexagon_conjecture

/-- `HasCollinear l P` says that some `l` points of `P` lie on a line. -/
def HasCollinear (l : ℕ) (P : Finset (ℝ × ℝ)) : Prop :=
  ∃ L ⊆ P, L.card = l ∧ Collinear ℝ (L : Set (ℝ × ℝ))

/--
`HasEmptyHexagon P` says that `P` contains an empty hexagon: a subset `S ⊆ P` of six points
in convex position (no point of `S` lies in the convex hull of the other five) with no other
point of `P` in the convex hull of `S`.
-/
def HasEmptyHexagon (P : Finset (ℝ × ℝ)) : Prop :=
  ∃ S ⊆ P, S.card = 6 ∧ ConvexIndependent ℝ ((↑) : ↥(S : Set (ℝ × ℝ)) → ℝ × ℝ) ∧
    ∀ p ∈ P, p ∈ convexHull ℝ (S : Set (ℝ × ℝ)) → p ∈ S

/--
For each `l ≥ 3` there is an integer `f(l)` such that every finite set of at least `f(l)` points
in the plane contains `l` collinear points or an empty hexagon.
-/
theorem main :
    ∀ l : ℕ, 3 ≤ l → ∃ f : ℕ, ∀ P : Finset (ℝ × ℝ),
      f ≤ P.card → HasCollinear l P ∨ HasEmptyHexagon P := by
  sorry

end OMA.S_opg_generalised_empty_hexagon_conjecture
