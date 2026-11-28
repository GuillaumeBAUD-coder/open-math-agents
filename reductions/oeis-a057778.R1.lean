import OMAStatements.S_oeis_a057778

-- Reduction oeis-a057778.R1 of oeis-a057778: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a057778_R1

open OMA.S_oeis_a057778

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → a n < 2 ^ n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (fun n : ℕ => (a n : ℝ)) =O[Filter.atTop] (fun n : ℕ => (n : ℝ) * Real.log n)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a057778.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a057778_R1
