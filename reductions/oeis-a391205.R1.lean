import OMAStatements.S_oeis_a391205

-- Reduction oeis-a391205.R1 of oeis-a391205: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a391205_R1

open OMA.S_oeis_a391205

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 1 ≤ n → a n ≤ 15

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → (a n = -1 ↔ ∃ j : ℕ, n = 10 ^ j)

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, 1 ≤ n → (a n = 15 ↔ ∃ j : ℕ, n = 2 * 10 ^ j)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a391205.main := by
  intro h1 h2 h3 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2, h3 x1 x2⟩

end OMA.R_oeis_a391205_R1
