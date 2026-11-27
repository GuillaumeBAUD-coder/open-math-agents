import Mathlib

/-!
# Kneser–Poulsen conjecture

Source: https://www.openproblemgarden.org/op/kneser_poulsen_conjecture
Credit: @lzvxck

The source: if a finite set of unit balls in `ℝ^n` is rearranged so that the distance between
each pair of centers does not decrease, then the volume of the union of the balls does not
decrease.

A finite family of unit balls is given by its centers `p : Fin N → ℝ^n`; a rearrangement is a
second family of centers `q : Fin N → ℝ^n` with `dist (p i) (p j) ≤ dist (q i) (q j)` for all
`i, j`. Volume is Lebesgue measure on `EuclideanSpace ℝ (Fin n)`. (Closed balls are used; open
balls have the same volume.)
-/

namespace OMA.S_opg_kneser_poulsen_conjecture

/-- The union of the closed unit balls centred at the points `p i`. -/
def unionOfUnitBalls {n N : ℕ} (p : Fin N → EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  ⋃ i, Metric.closedBall (p i) 1

/-- **Kneser–Poulsen conjecture.** If the centres of finitely many unit balls in `ℝ^n` are moved
so that no pairwise distance decreases, the volume of the union does not decrease. -/
theorem main : ∀ (n N : ℕ) (p q : Fin N → EuclideanSpace ℝ (Fin n)),
    (∀ i j, dist (p i) (p j) ≤ dist (q i) (q j)) →
      MeasureTheory.volume (unionOfUnitBalls p) ≤ MeasureTheory.volume (unionOfUnitBalls q) := by
  sorry

end OMA.S_opg_kneser_poulsen_conjecture
