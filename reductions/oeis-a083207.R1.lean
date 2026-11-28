import OMAStatements.S_oeis_a083207

-- Reduction oeis-a083207.R1 of oeis-a083207: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a083207_R1

open OMA.S_oeis_a083207

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → ∃ k, n ≤ k ∧ k < n + 12 ∧ IsZumkeller k)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ i : ℕ, ∃ j, i ≤ j ∧ j < i + 4 ∧ IsZumkeller (ArithmeticFunction.sigma 1 (Nat.nth IsZumkeller j) / 2))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ d k : ℕ, 1 < d → d ∣ k → d.divisors.card * ArithmeticFunction.sigma 1 d = k → IsZumkeller k)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a083207.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a083207_R1
