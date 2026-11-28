import OMAStatements.S_oeis_a136958

-- Reduction oeis-a136958.R1 of oeis-a136958: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a136958_R1

open OMA.S_oeis_a136958

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ k : ℕ, IsTerm k → 4 ∉ Nat.digits 10 k)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ k : ℕ, IsTerm k → k ≠ 0 → ∃ m : ℕ, k = 88 * 10 ^ m ∨ k = 878 * 10 ^ m)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a136958.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a136958_R1
