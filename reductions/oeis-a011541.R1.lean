import OMAStatements.S_oeis_a011541

-- Reduction oeis-a011541.R1 of oeis-a011541: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a011541_R1

open OMA.S_oeis_a011541

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 1 ≤ n → (Ta n).primeFactors.card < (Ta (n + 1)).primeFactors.card

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → (Ta n).primeFactors.card ≤ 2 * n

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a011541.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a011541_R1
