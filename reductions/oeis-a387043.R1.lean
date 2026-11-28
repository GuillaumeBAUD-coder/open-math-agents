import OMAStatements.S_oeis_a387043

-- Reduction oeis-a387043.R1 of oeis-a387043: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a387043_R1

open OMA.S_oeis_a387043

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 12 < n → ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧
        2 * n = p + prime k + prime (k + 1) + prime (k + 2))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 135 < n → ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧
        2 * n + 1 = 2 * p + prime k + prime (k + 1) + prime (k + 2)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a387043.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a387043_R1
