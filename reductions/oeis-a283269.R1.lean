import OMAStatements.S_oeis_a283269

-- Reduction oeis-a283269.R1 of oeis-a283269: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a283269_R1

open OMA.S_oeis_a283269

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ k m : ℕ, Odd k → Odd m → Rep (2 ^ k * m))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, ¬ Rep (4 * n + 1) ↔ n = 63)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ k m : ℕ, Odd k → Odd m → ∃ x y z s : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = 2 ^ k * m ∧
        x + 3 * y + 5 * z = 2 * s ^ 2)

/-- Step H4 of the reduction. -/
def H4 : Prop := ∀ n : ℕ, Odd n → n % 8 ≠ 7 → ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n ∧ IsSquare (x + 3 * y + 4 * z)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a283269.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a283269_R1
