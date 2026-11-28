import OMAStatements.S_wp_mcmullen_problem_on_projectively_transforming_sets_of_points_into_convex_positio

-- Reduction wp-mcmullen-problem-on-projectively-transforming-sets-of-points-into-convex-positio.R1 of wp-mcmullen-problem-on-projectively-transforming-sets-of-points-into-convex-positio: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_wp_mcmullen_problem_on_projectively_transforming_sets_of_points_into_convex_positio_R1

open OMA.S_wp_mcmullen_problem_on_projectively_transforming_sets_of_points_into_convex_positio

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ d : ℕ, 2 ≤ d → McMullenProp d (2 * d + 1)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ d : ℕ, 2 ≤ d → ∀ n : ℕ, 2 * d + 1 < n → ¬ McMullenProp d n

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_wp_mcmullen_problem_on_projectively_transforming_sets_of_points_into_convex_positio.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_wp_mcmullen_problem_on_projectively_transforming_sets_of_points_into_convex_positio_R1
