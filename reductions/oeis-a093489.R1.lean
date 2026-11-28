import OMAStatements.S_oeis_a093489

-- Reduction oeis-a093489.R1 of oeis-a093489: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a093489_R1

open OMA.S_oeis_a093489

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 3 < n → a n ≠ 0)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ k : ℕ, {n : ℕ | a n = k}.Finite

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a093489.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a093489_R1
