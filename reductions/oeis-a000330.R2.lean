import OMAStatements.S_oeis_a000330
import Mathlib

-- Reduction oeis-a000330.R2 of A000330.
-- Credit: @MBimrose
-- A000330 conjectures: every integer is a sum of three generalized square pyramidal numbers
-- (r = 4), and more strongly, every integer is a sum of three generalized r-gonal pyramidal
-- numbers for every r >= 3. "Generalized" means negative indices a, b, c are allowed.
-- Splitting by r (r = 3, r = 4, r >= 5) and, for r = 4, into a FINITE decideable window and
-- the two open tails isolates four sub-claims, H1 being a finite computation.

namespace OMA.R_oeis_a000330_R2

open OMA.S_oeis_a000330

/-- r = 4, the finite window `1 <= z <= 200`: decidable, the honest small-case computation that
the conjecture needs at the bottom of the range. -/
def H1 : Prop := ∀ z : ℤ, 1 ≤ z → z ≤ 200 → ∃ a b c : ℤ,
  z = generalizedPolygonalPyramidal 4 a + generalizedPolygonalPyramidal 4 b
    + generalizedPolygonalPyramidal 4 c

/-- r = 4, the open tails: every negative integer and every integer above the window. -/
def H2 : Prop := ∀ z : ℤ, (z < 0 ∨ 200 < z) → ∃ a b c : ℤ,
  z = generalizedPolygonalPyramidal 4 a + generalizedPolygonalPyramidal 4 b
    + generalizedPolygonalPyramidal 4 c

/-- r = 3 (tetrahedral numbers), all integers. -/
def H3 : Prop := ∀ z : ℤ, ∃ a b c : ℤ,
  z = generalizedPolygonalPyramidal 3 a + generalizedPolygonalPyramidal 3 b
    + generalizedPolygonalPyramidal 3 c

/-- r >= 5, all integers: the "stronger version" half of the conjecture. -/
def H4 : Prop := ∀ r : ℕ, 5 ≤ r → ∀ z : ℤ, ∃ a b c : ℤ,
  z = generalizedPolygonalPyramidal r a + generalizedPolygonalPyramidal r b
    + generalizedPolygonalPyramidal r c

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a000330.main := by
  intro h1 h2 h3 h4 r hr z
  rcases Nat.lt_or_ge r 5 with hsmall | hbig
  · rcases Nat.lt_or_ge r 4 with h3r | h4r
    · have hr3 : r = 3 := by omega
      subst hr3
      exact h3 z
    · have hr4 : r = 4 := by omega
      subst hr4
      rcases lt_trichotomy z 0 with hz | hz | hz
      · exact h2 z (Or.inl hz)
      · subst hz
        exact ⟨0, 0, 0, by simp [generalizedPolygonalPyramidal]⟩
      · by_cases hz' : z ≤ 200
        · exact h1 z (by omega) hz'
        · exact h2 z (Or.inr (by omega))
  · exact h4 r hbig z

end OMA.R_oeis_a000330_R2
