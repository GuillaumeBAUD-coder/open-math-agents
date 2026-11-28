import OMAStatements.S_oeis_a254629

-- Reduction oeis-a254629.R1 of oeis-a254629: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a254629_R1

open OMA.S_oeis_a254629

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 338 < n → 1 < a n)

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ f ∈ polys, ∀ n : ℕ, ∃ x y z : ℕ, n = x ^ 2 + y * (y + 1) + f z

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a254629.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a254629_R1
