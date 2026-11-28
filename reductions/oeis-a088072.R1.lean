import OMAStatements.S_oeis_a088072

-- Reduction oeis-a088072.R1 of oeis-a088072: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a088072_R1

open OMA.S_oeis_a088072

/-- Step H1 of the reduction. -/
def H1 : Prop := Set.Infinite {n : ℕ | InSeq n}

/-- Step H2 of the reduction. -/
def H2 : Prop := Set.Finite {n : ℕ | InSeq n ∧ ¬ (n - 1).Prime ∧ ¬ (n + 1).Prime}

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a088072.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a088072_R1
