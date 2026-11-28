import OMAStatements.S_oeis_a347205

-- Reduction oeis-a347205.R1 of oeis-a347205: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a347205_R1

open OMA.S_oeis_a347205

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, a347205 n = T347205 n (wt n + 1)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, a347205 (2 * n) = ∑ k ∈ Finset.Icc 1 (wt n + 1), T347205 n k

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a347205.main := by
  intro h1 h2 x1
  exact ⟨h1 x1, h2 x1⟩

end OMA.R_oeis_a347205_R1
