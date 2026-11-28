import OMAStatements.S_oeis_a360930

-- Reduction oeis-a360930.R1 of oeis-a360930: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a360930_R1

open OMA.S_oeis_a360930

/-- Step H1 of the reduction. -/
def H1 : Prop := ¬ Expressible 772277

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, n % 2 = 1 → 772277 < n → Expressible n

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a360930.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a360930_R1
