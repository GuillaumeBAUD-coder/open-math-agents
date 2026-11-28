import OMAStatements.S_oeis_a076957

-- Reduction oeis-a076957.R1 of oeis-a076957: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a076957_R1

open OMA.S_oeis_a076957

/-- Step H1 of the reduction. -/
def H1 : Prop := (¬ ∃ k : ℕ, 1 ≤ k ∧ c k = 1)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ c k = n

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a076957.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a076957_R1
