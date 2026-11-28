import OMAStatements.S_oeis_a006960

-- Reduction oeis-a006960.R1 of oeis-a006960: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a006960_R1

open OMA.S_oeis_a006960

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ k : ℕ, ¬ IsPalindrome (revAdd^[k] 196))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 0 < n → n < 196 → ∃ k : ℕ, IsPalindrome (revAdd^[k] n)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a006960.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a006960_R1
