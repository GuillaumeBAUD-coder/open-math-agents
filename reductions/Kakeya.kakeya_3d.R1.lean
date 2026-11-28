import FormalConjectures.Wikipedia.Kakeya
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
Reduction `Kakeya.kakeya_3d.R1` of the three-dimensional Kakeya set conjecture
(Wang and Zahl [WaZa25], arXiv:2502.17655).
Credit: @B221393

- `H1`: Direction-pigeonholing onto a bounded base ball: for every Kakeya set `S` in `R^3`,
  countable subadditivity of 2-dimensional Hausdorff measure on the unit sphere `S^2` yields
  a radius `R : N` for which the unit directions admitting a segment in `S` based in
  `closedBall 0 R` have positive `2`-dimensional Hausdorff measure.
- `H2`: Wang-Zahl [WaZa25] main lower bound for bounded-base Kakeya sets: any set in `R^3`
  containing unit segments based in `closedBall 0 R` for a positive-`muH[2]`-measure set of
  directions has Hausdorff dimension at least `3`.
- `main`: Proves the ambient upper bound `dimH S <= 3` unconditionally via `dimH_mono` and
  `dimH_univ_eq_finrank`, and combines `H1` and `H2` via `le_antisymm` to conclude `dimH S = 3`.
-/

namespace OMA.R_Kakeya_kakeya_3d_R1

open MeasureTheory Metric

/-- Direction-pigeonholing onto a bounded base ball: every Kakeya set in `R^3` admits a radius
`R` such that the set of unit directions whose segments lie in `S` with basepoint in
`closedBall 0 R` has strictly positive 2-dimensional Hausdorff measure. -/
def H1 : Prop :=
  ∀ S : Set (EuclideanSpace ℝ (Fin 3)), Kakeya.IsKakeya S →
    ∃ R : ℕ, 0 < MeasureTheory.Measure.hausdorffMeasure (2 : ℝ)
      {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1 ∧
        ∃ a ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (R : ℝ),
          affineSegment ℝ a (a + v) ⊆ S}

/-- Wang-Zahl [WaZa25] lower bound for bounded-base positive-direction-measure Kakeya sets:
if a set `S` in `R^3` contains unit segments based in `closedBall 0 R` across a set of unit
directions of positive 2-dimensional Hausdorff measure, then `3 <= dimH S`. -/
def H2 : Prop :=
  ∀ (R : ℕ) (S : Set (EuclideanSpace ℝ (Fin 3))),
    0 < MeasureTheory.Measure.hausdorffMeasure (2 : ℝ)
      {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1 ∧
        ∃ a ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (R : ℝ),
          affineSegment ℝ a (a + v) ⊆ S} →
    (3 : ENNReal) ≤ dimH S

theorem main : H1 → H2 → type_of% @Kakeya.kakeya_3d := by
  intro h1 h2 S hS
  obtain ⟨R, hRpos⟩ := h1 S hS
  have hge : (3 : ENNReal) ≤ dimH S := h2 R S hRpos
  have hle : dimH S ≤ (3 : ENNReal) := by
    calc dimH S
        ≤ dimH (Set.univ : Set (EuclideanSpace ℝ (Fin 3))) := dimH_mono (Set.subset_univ S)
      _ = (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ENNReal) :=
          Real.dimH_univ_eq_finrank (EuclideanSpace ℝ (Fin 3))
      _ = (3 : ENNReal) := by simp
  exact le_antisymm hle hge

end OMA.R_Kakeya_kakeya_3d_R1
