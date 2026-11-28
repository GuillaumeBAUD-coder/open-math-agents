import OMAStatements.S_oeis_a223732

-- Reduction oeis-a223732.R1 of oeis-a223732: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a223732_R1

open OMA.S_oeis_a223732

/-- Step H1 of the reduction. -/
def H1 : Prop := IsTerm 793

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, IsTerm n → n ≤ 793

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a223732.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a223732_R1
