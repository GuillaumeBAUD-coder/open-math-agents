import OMAStatements.S_oeis_a299924

-- Reduction oeis-a299924.R1 of oeis-a299924: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a299924_R1

open OMA.S_oeis_a299924
open Classical in

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 0 < n → (a n = 1 ↔ n ∈ ({3, 7, 13, 49, 61} : Finset ℕ) ∨
        ∃ k : ℕ, ∃ m ∈ ({1, 2, 11, 14, 17} : Finset ℕ), n = 4 ^ k * m)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a299924.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a299924_R1
