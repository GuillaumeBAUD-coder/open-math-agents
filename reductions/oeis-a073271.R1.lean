import OMAStatements.S_oeis_a073271

-- Reduction oeis-a073271.R1 of oeis-a073271: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a073271_R1

open OMA.S_oeis_a073271

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → (Odd (a n) ↔ n = 1 ∨ n = 3 ∨ n = 8))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 1 ≤ n → a n = a (n + 1) → gap (n + 1) = gap n + gap (n + 2))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a073271.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a073271_R1
