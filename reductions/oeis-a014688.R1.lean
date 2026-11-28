import OMAStatements.S_oeis_a014688

-- Reduction oeis-a014688.R1 of oeis-a014688: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a014688_R1

open OMA.S_oeis_a014688

/-- Step H1 of the reduction. -/
def H1 : Prop := {n : ℕ | 1 ≤ n ∧ (Nat.nth Nat.Prime (n - 1) + n).Prime}.Infinite

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ L : ℕ, ∃ n : ℕ, 1 ≤ n ∧ ∀ j < L, ¬ (Nat.nth Nat.Prime (n + j - 1) + (n + j)).Prime

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a014688.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a014688_R1
