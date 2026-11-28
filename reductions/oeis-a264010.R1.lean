import OMAStatements.S_oeis_a264010

-- Reduction oeis-a264010.R1 of oeis-a264010: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a264010_R1

open OMA.S_oeis_a264010

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 2 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ)))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 2 < n → ∃ x y z : ℕ, PP x ∧ PP y ∧
        x * (x + 1) + y * (y + 1) / 2 + z * (z + 1) / 2 = n)

/-- Step H4 of the reduction. -/
def H4 : Prop := ( ∀ n : ℕ, 7 < n → ∃ x y z : ℕ, PP y ∧ PP z ∧ x * (x + 1) + y * (y + 1) / 2 + 3 * (z * (z + 1) / 2) = n )

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a264010.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a264010_R1
