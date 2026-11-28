import OMAStatements.S_oeis_a248004

-- Reduction oeis-a248004.R1 of oeis-a248004: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a248004_R1

open OMA.S_oeis_a248004

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ prime (m * n) ≡ 1 [MOD m + n])

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 2 < n → ∃ m : ℕ, 0 < m ∧ m ≤ n * (n - 1) / 2 ∧ prime (m * n) ≡ 1 [MOD m + n])

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ prime (m * n) + 1)

/-- Step H4 of the reduction. -/
def H4 : Prop := ( ∀ n : ℕ, 2 < n → ∃ m : ℕ, 0 < m ∧ m ≤ n * (n - 1) / 2 ∧ m + n ∣ prime (m * n) + 1 )

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a248004.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a248004_R1
