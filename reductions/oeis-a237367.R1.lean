import OMAStatements.S_oeis_a237367

-- Reduction oeis-a237367.R1 of oeis-a237367: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a237367_R1

open OMA.S_oeis_a237367

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 2 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n ∈ ({3, 73, 81, 534} : Finset ℕ)))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 2 < n → ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ n = k + m ∧ (2 * k - 1).Prime ∧
      (prime k + k * (k - 1)).Prime ∧ (prime m + m * (m - 1)).Prime)

/-- Step H4 of the reduction. -/
def H4 : Prop := (∀ n : ℕ, 9 ≤ n → ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ n = k + m ∧ (6 * k - 1).Prime ∧
      (prime k + 2 * k).Prime ∧ (prime m + 2 * m).Prime)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a237367.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a237367_R1
