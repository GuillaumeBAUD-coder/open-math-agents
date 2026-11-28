import OMAStatements.S_oeis_a214342

-- Reduction oeis-a214342.R1 of oeis-a214342: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a214342_R1

open OMA.S_oeis_a214342

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ i : ℕ, 8 ≤ i → (descendants (Nat.nth Nat.Prime i)).Finite

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ i : ℕ, 8 ≤ i → (descendants (Nat.nth Nat.Prime i)).ncard ≤ 35

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a214342.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a214342_R1
