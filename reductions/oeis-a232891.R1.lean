import OMAStatements.S_oeis_a232891

-- Reduction oeis-a232891.R1 of oeis-a232891: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a232891_R1

open OMA.S_oeis_a232891

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → ∀ r : ℕ, r < n → ∃ k : ℕ, 1 ≤ k ∧ 2 * k ≤ n ^ 2 + 6 ∧
        (k * Nat.nth Nat.Prime (k - 1)) % n = r)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 0 < n → n ≠ 3 → ¬ ∃ x m : ℕ, 1 < m ∧ n * Nat.nth Nat.Prime (n - 1) + 1 = x ^ m

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a232891.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a232891_R1
