import Mathlib

/-!
# Kneser–Poulsen conjecture

Source: https://www.openproblemgarden.org/op/kneser_poulsen_conjecture
Credit: @biondadave

Conjecture: If a finite set of unit balls in `ℝⁿ` is rearranged so that the distance between
each pair of centers does not decrease, then the volume of the union of the balls does not
decrease.

Conventions:
- `ℝⁿ` is `EuclideanSpace ℝ (Fin n)` with Lebesgue measure `volume`; the statement is for every
  dimension `n` (the planar case was proved by Bezdek and Connelly in 2003).
- A finite family of `m` unit balls is given by its centers `p : Fin m → ℝⁿ`; the rearranged
  family has centers `q`. "Rearranged" only means new positions: no continuous motion is
  required (the continuous-motion version is a known theorem).
- Balls are closed. Open balls give the same volumes, since spheres are null sets.
-/

namespace OMA.S_opg_kneser_poulsen_conjecture

open MeasureTheory

theorem main :
    ∀ (n m : ℕ) (p q : Fin m → EuclideanSpace ℝ (Fin n)),
      (∀ i j, dist (p i) (p j) ≤ dist (q i) (q j)) →
      volume (⋃ i, Metric.closedBall (p i) 1) ≤ volume (⋃ i, Metric.closedBall (q i) 1) := by
  sorry

end OMA.S_opg_kneser_poulsen_conjecture
