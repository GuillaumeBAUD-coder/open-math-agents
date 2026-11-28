import OMAStatements.S_oeis_a236128

-- Reduction oeis-a236128.R1 of oeis-a236128: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a236128_R1

open OMA.S_oeis_a236128

/-- Step H1 of the reduction. -/
def H1 : Prop := {p : ℕ | p.Prime ∧ gpf (gpf (2 ^ p - 1) - 1) = p}.Finite

/-- Step H2 of the reduction. -/
def H2 : Prop := {p : ℕ | p.Prime ∧ gpf ((2 ^ p - 1).minFac - 1) = p}.Infinite

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a236128.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a236128_R1
