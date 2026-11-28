import OMAStatements.S_oeis_a232502

-- Reduction oeis-a232502.R1 of oeis-a232502: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a232502_R1

open OMA.S_oeis_a232502

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 4 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n ∈ ({5, 6, 7, 9, 11, 14, 17, 21, 34, 43} : Finset ℕ)))

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, 4 < n → ∃ k, 0 < k ∧ 2 * k < n ∧ (2 * prime (n - k) + prime k).Prime

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a232502.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a232502_R1
