import OMAStatements.S_oeis_a098472

-- Reduction oeis-a098472.R1 of oeis-a098472: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a098472_R1

open OMA.S_oeis_a098472

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ k : ℕ, 1 ≤ k → ¬ Nat.Prime (mersennePrime 12 * 2 ^ k - 1)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ k : ℕ, 1 ≤ k → ¬ Nat.Prime (mersennePrime 14 * 2 ^ k - 1)

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ k : ℕ, 1 ≤ k → ¬ Nat.Prime (mersennePrime 15 * 2 ^ k - 1)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a098472.main := by
  intro h1 h2 h3 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2, h3 x1 x2⟩

end OMA.R_oeis_a098472_R1
