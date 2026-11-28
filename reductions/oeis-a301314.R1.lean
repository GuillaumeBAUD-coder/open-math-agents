import OMAStatements.S_oeis_a301314

-- Reduction oeis-a301314.R1 of oeis-a301314: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a301314_R1

open OMA.S_oeis_a301314

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < w ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        ∃ k m : ℕ, x + 3 * y + 9 * z = 2 ^ k * m ^ 3)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < x ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        ∃ k m : ℕ, k ≤ 2 ∧ 0 < m ∧ 2 * x + 7 * y = 2 ^ k * m ^ 3

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a301314.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a301314_R1
