import OMAStatements.S_oeis_a248568

-- Reduction oeis-a248568.R1 of oeis-a248568: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a248568_R1

open OMA.S_oeis_a248568

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ Nat.totient (m + n) ∣ m)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 < n → ∃ m : ℕ, 0 < m ∧ m ≤ n * (n - 1) ∧ Nat.totient (m + n) ∣ m

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a248568.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a248568_R1
