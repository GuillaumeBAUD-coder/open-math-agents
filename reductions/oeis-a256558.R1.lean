import OMAStatements.S_oeis_a256558

-- Reduction oeis-a256558.R1 of oeis-a256558: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a256558_R1

open OMA.S_oeis_a256558

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 < n → ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ n = p + k * (k + 1) / 4)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ m : ℕ, 4 < m → m ≠ 12 → ∀ n : ℕ, 1 < n →
        ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ n = p + (k ^ 2 - 1) / m

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a256558.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a256558_R1
