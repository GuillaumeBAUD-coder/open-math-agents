import OMAStatements.S_mse_2431879

-- Reduction mse-2431879.R1 of mse-2431879: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_mse_2431879_R1

open OMA.S_mse_2431879

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ O : ℕ, 5 ≤ O → Odd O → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ 2 ∧ q ≠ 2 ∧ p ≠ q ∧
      (O : ℤ) = p - 2 * q)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ O : ℕ, 1 ≤ O → Odd O → ∃ p q : ℕ, p.Prime ∧ p ≠ 2 ∧ (q = 1 ∨ (q.Prime ∧ q ≠ 2)) ∧ q < p ∧
      (O : ℤ) = 2 * q - p)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_mse_2431879.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_mse_2431879_R1
