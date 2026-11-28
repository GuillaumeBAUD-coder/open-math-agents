import OMAStatements.S_oeis_a140320

-- Reduction oeis-a140320.R1 of oeis-a140320: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a140320_R1

open OMA.S_oeis_a140320

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, a137576 ((3 ^ n - 1) / 2) = 2 * n * 3 ^ (n - 1) + 1)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 2 * n + 1 ≤ a137576 n)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, (2 * n + 1).Prime → a137576 n = 2 * n + 1)

/-- Step H4 of the reduction. -/
def H4 : Prop := ( (∀ N : ℕ, ∃ n ≥ N, a137576 n = 2 * n + 1) ∧ (∀ B N : ℕ, ∃ n : ℕ, N ≤ n ∧ B * n < a137576 n) )

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a140320.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a140320_R1
