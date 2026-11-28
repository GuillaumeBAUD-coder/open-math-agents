import OMAStatements.S_oeis_a231516

-- Reduction oeis-a231516.R1 of oeis-a231516: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a231516_R1

open OMA.S_oeis_a231516

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 < n →
      ∃ x y : ℕ, 0 < x ∧ x ≤ y ∧ x + y = n ∧ Nat.Prime (x.factorial * y + 1))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 3 < n →
      ∃ x y : ℕ, 0 < x ∧ x ≤ y ∧ x + y = n ∧ Nat.Prime (x.factorial * y - 1))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a231516.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a231516_R1
