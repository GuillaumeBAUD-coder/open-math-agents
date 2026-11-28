import OMAStatements.S_oeis_a260082

-- Reduction oeis-a260082.R1 of oeis-a260082: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a260082_R1

open OMA.S_oeis_a260082

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → ∃ i j k : ℕ, 0 < i ∧ i < j ∧ 0 < k ∧
        (prime (k * n) - 1) ^ 2 = (prime (i * n) - 1) * (prime (j * n) - 1))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ m : ℤ, m ≠ 0 → ∀ n : ℕ, 1 ≤ n → ∃ i j k : ℕ, 1 ≤ i ∧ 1 ≤ j ∧ 1 ≤ k ∧
        i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        ((prime (i * n) : ℤ) + m) * ((prime (j * n) : ℤ) + m) = ((prime (k * n) : ℤ) + m) ^ 2

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a260082.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a260082_R1
