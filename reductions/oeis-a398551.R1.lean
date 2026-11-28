import OMAStatements.S_oeis_a398551

-- Reduction oeis-a398551.R1 of oeis-a398551: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a398551_R1

open OMA.S_oeis_a398551

/-- Step H1 of the reduction. -/
def H1 : Prop := (¬ ∃ p q : ℕ, IsIsolated p ∧ IsIsolated q ∧ p + q = 628)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 628 < n → Even n → ∃ p q : ℕ, IsIsolated p ∧ IsIsolated q ∧ p + q = n

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a398551.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a398551_R1
