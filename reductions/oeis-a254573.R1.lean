import OMAStatements.S_oeis_a254573

-- Reduction oeis-a254573.R1 of oeis-a254573: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a254573_R1

open OMA.S_oeis_a254573

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, a n = 1 ↔ n ∈ ({0, 1, 4, 6, 10, 11, 23} : Finset ℕ)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a254573.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a254573_R1
