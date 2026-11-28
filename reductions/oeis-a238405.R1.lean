import OMAStatements.S_oeis_a238405

-- Reduction oeis-a238405.R1 of oeis-a238405: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a238405_R1

open OMA.S_oeis_a238405
open Classical

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 6 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, a n = 1 ↔ n ∈ ({5, 7, 13, 16, 18, 24, 29, 71, 72, 158} : Finset ℕ)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a238405.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a238405_R1
