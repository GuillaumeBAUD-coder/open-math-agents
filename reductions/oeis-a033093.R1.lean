import OMAStatements.S_oeis_a033093

-- Reduction oeis-a033093.R1 of oeis-a033093: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a033093_R1

open OMA.S_oeis_a033093
open Filter

/-- Step H1 of the reduction. -/
def H1 : Prop := Tendsto a atTop atTop

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n = 2 ∨ n = 3 ∨ n = 7)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a033093.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a033093_R1
