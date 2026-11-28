import OMAStatements.S_oeis_a255807

-- Reduction oeis-a255807.R1 of oeis-a255807: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a255807_R1

open OMA.S_oeis_a255807

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, a (n + 5) % 10 = a n % 10)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ k : ℕ, 2 ≤ k → ∀ n : ℕ, a (n + k) ≡ a n [MOD k])

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a255807.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a255807_R1
