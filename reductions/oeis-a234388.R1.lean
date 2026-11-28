import OMAStatements.S_oeis_a234388

-- Reduction oeis-a234388.R1 of oeis-a234388: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a234388_R1

open OMA.S_oeis_a234388

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 < n → ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ k + m = n ∧
        (2 ^ k * (2 ^ Nat.totient m - 1) + 1).Prime)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 2 < n → ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ k + m = n ∧
        (2 ^ k * (2 ^ Nat.totient m - 1) - 1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a234388.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a234388_R1
