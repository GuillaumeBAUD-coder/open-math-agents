import OMAStatements.S_oeis_a076980

-- Reduction oeis-a076980.R1 of oeis-a076980: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a076980_R1

open OMA.S_oeis_a076980

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ d : ℕ, 11 < d →
      sInf {m : ℕ | IsLeyland m ∧ 10 ^ (d - 1) ≤ m ∧ m < 10 ^ d} = 10 ^ (d - 1) + (d - 1) ^ 10)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 0 < n → ∃ p : ℕ, Nat.Prime p ∧ a n ≤ p + 1 ∧ p + 1 < a (n + 1))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 0 < n → n ≠ 5 → ∃ p : ℕ, Nat.Prime p ∧ a n < p ∧ p < a (n + 1))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a076980.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a076980_R1
