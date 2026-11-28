import OMAStatements.S_oeis_a308934

-- Reduction oeis-a308934.R1 of oeis-a308934: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a308934_R1

open OMA.S_oeis_a308934

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 < n → ∃ a b c d x y : ℕ,
        (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 3 ^ d) ^ 2 + x ^ 2 + 2 * y ^ 2 = n)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 < n → ∃ a b c d x y : ℕ,
        (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 + x ^ 2 + 2 * y ^ 2 = n

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a308934.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a308934_R1
