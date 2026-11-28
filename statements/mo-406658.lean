import Mathlib

namespace OMA.S_mo_406658

open MeasureTheory

universe u

/-- The complex Haar L² space of a locally compact Hausdorff group has an
orthonormal basis with compactly supported continuous representatives. -/
theorem main :
    ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
      (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure] [μ.Regular],
      ∃ (ι : Type u) (basis : HilbertBasis ι ℂ (Lp ℂ 2 μ)),
        ∀ i, ∃ f : ContinuousMap G ℂ,
          HasCompactSupport f ∧ (basis i : G → ℂ) =ᵐ[μ] f := by
  sorry

end OMA.S_mo_406658
