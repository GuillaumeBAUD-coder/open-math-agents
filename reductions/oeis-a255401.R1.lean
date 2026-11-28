import OMAStatements.S_oeis_a255401

-- Reduction oeis-a255401.R1 of oeis-a255401: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a255401_R1

open OMA.S_oeis_a255401

/-- Step H1 of the reduction. -/
def H1 : Prop := Set.Infinite {m : ℕ | HasDivisorDigitProperty m}

/-- Step H2 of the reduction. -/
def H2 : Prop := IsGreatest {k : ℕ | ∃ m : ℕ, HasDivisorDigitProperty m ∧ m.divisors.card = k} 8

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a255401.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a255401_R1
