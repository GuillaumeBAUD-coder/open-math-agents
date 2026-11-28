import OMAStatements.S_oeis_a271365

-- Reduction oeis-a271365.R1 of oeis-a271365: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a271365_R1

open OMA.S_oeis_a271365

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 1 ≤ n → 0 < a n

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → (a n = 1 →
      n ∈ ({1, 8, 15, 16, 23, 24, 56} : Finset ℕ))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a271365.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a271365_R1
