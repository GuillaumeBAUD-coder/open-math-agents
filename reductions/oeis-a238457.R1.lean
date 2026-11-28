import OMAStatements.S_oeis_a238457

-- Reduction oeis-a238457.R1 of oeis-a238457: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a238457_R1

open OMA.S_oeis_a238457

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 0 < n → (a n = 1 ↔ n ∈ ({1, 2, 3, 4, 5, 30, 109} : Finset ℕ)))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 2 < n → ∃ k, 0 < k ∧ k ≤ n + 3 ∧ (p n - k).Prime)

/-- Step H4 of the reduction. -/
def H4 : Prop := ( (∀ n : ℕ, 0 < n → ∃ k, 0 < k ∧ k ≤ n ∧ (q n + k).Prime) ∧ ∀ n : ℕ, 4 < n → ∃ k, 0 < k ∧ k ≤ n ∧ (q n - k).Prime )

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a238457.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a238457_R1
