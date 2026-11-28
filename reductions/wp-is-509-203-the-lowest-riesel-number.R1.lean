import OMAStatements.S_wp_is_509_203_the_lowest_riesel_number

-- Reduction wp-is-509-203-the-lowest-riesel-number.R1 of wp-is-509-203-the-lowest-riesel-number: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_wp_is_509_203_the_lowest_riesel_number_R1

open OMA.S_wp_is_509_203_the_lowest_riesel_number

/-- Step H1 of the reduction. -/
def H1 : Prop := IsRieselNumber 509203

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ k : ℕ, k < 509203 → ¬ IsRieselNumber k

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_wp_is_509_203_the_lowest_riesel_number.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_wp_is_509_203_the_lowest_riesel_number_R1
