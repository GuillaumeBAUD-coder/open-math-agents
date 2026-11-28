import OMAStatements.S_mse_3271457

-- Reduction mse-3271457.R1 of mse-3271457: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_mse_3271457_R1

open OMA.S_mse_3271457
open scoped BigOperators

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → ((primePowerSum n).Prime ↔ n = 2 ∨ n = 4 ∨ n = 24))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 0 < n →
        ((alternatingPrimePowerSum n).toNat.Prime ↔ n = 2 ∨ n = 4))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_mse_3271457.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_mse_3271457_R1
