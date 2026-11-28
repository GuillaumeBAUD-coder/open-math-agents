import OMAStatements.S_oeis_a238766

-- Reduction oeis-a238766.R1 of oeis-a238766: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a238766_R1

open OMA.S_oeis_a238766

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 1 < n → a n = 1 → n ∈ ({2, 3, 11, 44, 55, 149, 371} : Finset ℕ))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a238766.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a238766_R1
