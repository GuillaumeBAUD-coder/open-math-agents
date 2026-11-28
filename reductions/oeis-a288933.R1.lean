import OMAStatements.S_oeis_a288933

-- Reduction oeis-a288933.R1 of oeis-a288933: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a288933_R1

open OMA.S_oeis_a288933

/-- Step H1 of the reduction. -/
def H1 : Prop := Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) Filter.atTop (nhds 3)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 1 ≤ n → 0 < 3 - (a n : ℝ) / n ∧ 3 - (a n : ℝ) / n < 1)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 1 ≤ n → (a n : ℤ) = 3*(n : ℤ)-1-((Nat.digits 2 (n-1)).sum : ℤ))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a288933.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a288933_R1
