import OMAStatements.S_oeis_a344338

-- Reduction oeis-a344338.R1 of oeis-a344338: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a344338_R1

open OMA.S_oeis_a344338

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 4 ≤ n → ∀ N a l a' l' : ℕ, IsRep n N a l → IsRep n N a' l' → a = a'

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 4 ≤ n → ∀ N a l a' l' : ℕ, IsRep n N a l → IsRep n N a' l' → l = l'

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a344338.main := by
  intro h1 h2 x1 x2 x3 x4 x5 x6 x7 x8 x9
  exact ⟨h1 x1 x2 x3 x4 x5 x6 x7 x8 x9, h2 x1 x2 x3 x4 x5 x6 x7 x8 x9⟩

end OMA.R_oeis_a344338_R1
