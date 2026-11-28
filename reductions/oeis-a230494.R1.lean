import OMAStatements.S_oeis_a230494

-- Reduction oeis-a230494.R1 of oeis-a230494: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a230494_R1

open OMA.S_oeis_a230494

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 1 < n → n ≠ 2 → n ≠ 69 → n ≠ 76 →
        ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ^ 2 + y = n ∧ (2 * y ^ 2 - 1).Prime)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 1 < n → ∃ x y : ℕ, x * (x + 1) / 2 + y = n ∧ (2 * y ^ 2 - 1).Prime)

/-- Step H4 of the reduction. -/
def H4 : Prop := ∀ n : ℕ, 1 < n → n ≠ 2 → n ≠ 15 →
        ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x * (x + 1) / 2 + y = n ∧ (2 * y ^ 2 - 1).Prime

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a230494.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a230494_R1
