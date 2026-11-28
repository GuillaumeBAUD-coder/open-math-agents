import OMAStatements.S_oeis_a067182

-- Reduction oeis-a067182.R1 of oeis-a067182: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a067182_R1

open OMA.S_oeis_a067182

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, digitSum (Nat.fib n) ≤ n + 92)

/-- Step H2 of the reduction. -/
def H2 : Prop := digitSum (Nat.fib 2619) = 2619 + 92

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a067182.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a067182_R1
