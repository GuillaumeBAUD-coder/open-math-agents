import OMAStatements.S_oeis_a230022

-- Reduction oeis-a230022.R1 of oeis-a230022: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a230022_R1

open OMA.S_oeis_a230022

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → n - 1 ≤ a n ^ 2 ∧ (a n ^ 2 = n - 1 ↔ n = 2 ∨ n = 26))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ m : ℕ, 0 < m → ∃ n, 0 < n ∧ a n = m

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a230022.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a230022_R1
