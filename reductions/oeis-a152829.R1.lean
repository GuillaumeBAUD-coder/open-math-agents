import OMAStatements.S_oeis_a152829

-- Reduction oeis-a152829.R1 of oeis-a152829: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a152829_R1

open OMA.S_oeis_a152829

/-- Step H1 of the reduction. -/
def H1 : Prop := {k : ℕ | r (k ^ 2) = 1 ∧ Odd k} = {3, 7, 13}

/-- Step H2 of the reduction. -/
def H2 : Prop := {k : ℕ | r (k ^ 2) = 1} =
      {3, 6, 7} ∪ {k : ℕ | ∃ c j : ℕ, (c = 12 ∨ c = 13 ∨ c = 14) ∧ k = c * 2 ^ j}

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a152829.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a152829_R1
