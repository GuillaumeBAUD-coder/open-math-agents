import OMAStatements.S_oeis_a260140

-- Reduction oeis-a260140.R1 of oeis-a260140: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a260140_R1

open OMA.S_oeis_a260140

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
        Nat.primeCounting (p * n) = Nat.primeCounting (q * n) ^ 2)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ a b c : ℤ, 0 < a → ∀ n : ℕ, 1 ≤ n →
        ∃ x ∈ T n, ∃ y ∈ T n, a * x ^ 2 + b * x + c = y)

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ b c : ℤ, 0 < b → ∀ n : ℕ, 1 ≤ n → ∃ x ∈ T n, ∃ y ∈ T n, b * x + c = y

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a260140.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a260140_R1
