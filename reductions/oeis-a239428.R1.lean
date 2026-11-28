import OMAStatements.S_oeis_a239428

-- Reduction oeis-a239428.R1 of oeis-a239428: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a239428_R1

open OMA.S_oeis_a239428

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 9 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n ∈ ([8, 10, 11, 26, 33, 50, 52] : List ℕ)))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a239428.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a239428_R1
