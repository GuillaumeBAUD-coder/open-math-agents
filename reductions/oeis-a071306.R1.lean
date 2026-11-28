import OMAStatements.S_oeis_a071306

-- Reduction oeis-a071306.R1 of oeis-a071306: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a071306_R1

open OMA.S_oeis_a071306

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 4 ≤ n →
      (b n : ℤ) = 7 * (b (n - 1) : ℤ) - 7 * (b (n - 2) : ℤ) + 49 * (b (n - 3) : ℤ))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 1 ≤ n → a (n + 1) = a n * b (n + 1))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a071306.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a071306_R1
