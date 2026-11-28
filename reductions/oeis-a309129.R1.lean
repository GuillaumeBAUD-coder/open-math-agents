import OMAStatements.S_oeis_a309129

-- Reduction oeis-a309129.R1 of oeis-a309129: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a309129_R1

open OMA.S_oeis_a309129

/-- Step H1 of the reduction. -/
def H1 : Prop := IsTerm 1848

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ k : ℕ, 1848 < k → ¬ IsTerm k

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a309129.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a309129_R1
