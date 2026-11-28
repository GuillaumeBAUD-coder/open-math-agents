import OMAStatements.S_oeis_a224487

-- Reduction oeis-a224487.R1 of oeis-a224487: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a224487_R1

open OMA.S_oeis_a224487

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 < n → ∃ b : ℕ, Nat.fib n < b ∧ b < Nat.fib (n + 4) ∧ (S n b).Prime)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 1 < n → {b : ℕ | Nat.fib n < b ∧ (S n b).Prime}.Infinite)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a224487.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a224487_R1
