import OMAStatements.S_oeis_a360822

-- Reduction oeis-a360822.R1 of oeis-a360822: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a360822_R1

open OMA.S_oeis_a360822

/-- Step H1 of the reduction. -/
def H1 : Prop := Set.ncard {n : ℕ | IsTerm n} = 72

/-- Step H2 of the reduction. -/
def H2 : Prop := IsGreatest {n : ℕ | IsTerm n} 940206833

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a360822.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a360822_R1
