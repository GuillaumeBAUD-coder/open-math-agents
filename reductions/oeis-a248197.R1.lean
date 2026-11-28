import OMAStatements.S_oeis_a248197

-- Reduction oeis-a248197.R1 of oeis-a248197: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a248197_R1

open OMA.S_oeis_a248197

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ prime (prime m) + prime (prime n))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 2 < n → ∃ m : ℕ, 0 < m ∧ m < n * (n - 1) ∧ m + n ∣ prime (prime m) + prime (prime n)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a248197.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a248197_R1
