import OMAStatements.S_oeis_a023108

-- Reduction oeis-a023108.R1 of oeis-a023108: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a023108_R1

open OMA.S_oeis_a023108

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ x : ℕ, 0 < x → x < 196 → ∃ k, IsPalindrome (T^[k] x))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ k, ¬ IsPalindrome (T^[k] 196)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a023108.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a023108_R1
