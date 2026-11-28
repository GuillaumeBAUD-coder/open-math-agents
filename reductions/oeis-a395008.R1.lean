import OMAStatements.S_oeis_a395008

-- Reduction oeis-a395008.R1 of oeis-a395008: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a395008_R1

open OMA.S_oeis_a395008

/-- Step H1 of the reduction. -/
def H1 : Prop := (List.range 12).map (fun i => a (i + 1)) = [1, 4, 10, 16, 37, 58, 64, 130, 148, 232, 256, 445]

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 13 ≤ n → a n = 4 * a (n - 5)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a395008.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a395008_R1
