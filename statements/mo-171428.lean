import Mathlib.Topology.MetricSpace.HausdorffDimension

namespace OMA.S_mo_171428

open MeasureTheory

/-- Does there exist a full-dimensional additive subgroup of the reals with
no subgroup of intermediate Hausdorff dimension? -/
theorem main :
    ∃ G : AddSubgroup ℝ, dimH (G : Set ℝ) = 1 ∧
      ∀ H : AddSubgroup ℝ, H ≤ G → ¬ (0 < dimH (H : Set ℝ) ∧ dimH (H : Set ℝ) < 1) := by
  sorry

end OMA.S_mo_171428
