import Mathlib

-- Toeplitz' conjecture (inscribed square problem, square peg problem)
-- Source: https://en.wikipedia.org/wiki/Inscribed_square_problem (redirect target of
-- Toeplitz'_conjecture)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
Source: let `C` be a Jordan curve; a polygon is inscribed in `C` if all its vertices belong to
`C`. Does every Jordan curve admit an inscribed square? The vertices need not appear along the
curve in any particular order. Stated here in the affirmative.

Conventions:
* The plane is `ℂ`. A Jordan curve (plane simple closed curve) is the image of a continuous
  injective map `γ : Circle → ℂ` from Mathlib's unit circle.
* A square is non-degenerate, with vertices `a, a + v, a + v + i v, a + i v` for some `a` and some
  `v ≠ 0` (multiplication by `i` is the rotation by a right angle); every square in the plane has
  this form, listing its vertices in counterclockwise order from some vertex.
-/

namespace OMA.S_wp_toeplitz_conjecture

open Complex

/-- Every Jordan curve in the plane has an inscribed square. -/
theorem main : ∀ γ : Circle → ℂ, Continuous γ → Function.Injective γ →
    ∃ a v : ℂ, v ≠ 0 ∧ a ∈ Set.range γ ∧ a + v ∈ Set.range γ ∧ a + v + I * v ∈ Set.range γ ∧
      a + I * v ∈ Set.range γ := by
  sorry

end OMA.S_wp_toeplitz_conjecture
