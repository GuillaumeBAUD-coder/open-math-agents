import OMAStatements.S_oeis_a259544

-- Reduction oeis-a259544.R1 of oeis-a259544: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a259544_R1

open OMA.S_oeis_a259544
open scoped BigOperators

/-- Step H1 of the reduction. -/
def H1 : Prop := (a 4 = 7 ∧ ∀ n : ℕ, 0 < n → (a n < 2 ^ (n - 1) ↔ n = 4))

/-- Step H2 of the reduction. -/
def H2 : Prop := Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (2 : ℝ) ^ n) Filter.atTop Filter.atTop

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a259544.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a259544_R1
