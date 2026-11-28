import OMAStatements.S_oeis_a305502

-- Reduction oeis-a305502.R1 of oeis-a305502: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a305502_R1

open OMA.S_oeis_a305502

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, a n = 1 ↔
      n ∈ ({2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 16, 20, 22, 28, 42, 50} : Finset ℕ))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a305502.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a305502_R1
