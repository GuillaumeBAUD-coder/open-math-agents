import OMAStatements.S_oeis_a089610

-- Reduction oeis-a089610.R1 of oeis-a089610: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a089610_R1

open OMA.S_oeis_a089610

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 17 < n → 1 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → a n < a (n + 1))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 0 < n → 0 < a n)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a089610.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a089610_R1
