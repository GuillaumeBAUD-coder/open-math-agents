import OMAStatements.S_opg_asymptotic_distribution_of_form_of_polyhedra

-- Reduction opg-asymptotic-distribution-of-form-of-polyhedra.R1 of opg-asymptotic-distribution-of-form-of-polyhedra: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_opg_asymptotic_distribution_of_form_of_polyhedra_R1

open OMA.S_opg_asymptotic_distribution_of_form_of_polyhedra
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ f : BoundedContinuousFunction ℝ ℝ, Tendsto (fun e => uniformAverage e (fun v => f (form e v)))
        admissibleEdgeLimit (𝓝 (f (1 / 2)))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ f : BoundedContinuousFunction ℝ ℝ, Tendsto (fun e => uniformAverage e
          (fun v => f (Real.sqrt e * (form e v - 1 / 2))))
        admissibleEdgeLimit (𝓝 (∫ x, f x ∂(gaussianReal 0 ((1 : ℝ≥0) / 32))))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_opg_asymptotic_distribution_of_form_of_polyhedra.main := by
  intro h1 h2 x1
  exact ⟨h1 x1, h2 x1⟩

end OMA.R_opg_asymptotic_distribution_of_form_of_polyhedra_R1
