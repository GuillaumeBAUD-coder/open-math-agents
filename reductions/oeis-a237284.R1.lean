import OMAStatements.S_oeis_a237284

-- Reduction oeis-a237284.R1 of oeis-a237284: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a237284_R1

open OMA.S_oeis_a237284

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 2 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 2 < n → a n = 1 → n ∈ ({3, 6, 13, 16, 19, 28, 34, 40, 61, 166, 278} : Finset ℕ))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a237284.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a237284_R1
