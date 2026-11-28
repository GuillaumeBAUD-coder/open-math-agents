import OMAStatements.S_oeis_a248354

-- Reduction oeis-a248354.R1 of oeis-a248354: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a248354_R1

open OMA.S_oeis_a248354

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧
        m + n ∣ Nat.nth Nat.Prime (m ^ 2 - 1) + Nat.nth Nat.Prime (n ^ 2 - 1))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 < n → ∃ m : ℕ, 0 < m ∧ m ≤ n * (n - 1) / 2 ∧
        m + n ∣ Nat.nth Nat.Prime (m ^ 2 - 1) + Nat.nth Nat.Prime (n ^ 2 - 1)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a248354.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a248354_R1
