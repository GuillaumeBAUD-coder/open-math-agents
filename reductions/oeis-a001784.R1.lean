import OMAStatements.S_oeis_a001784

-- Reduction oeis-a001784.R1 of oeis-a001784: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a001784_R1

open OMA.S_oeis_a001784

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 4 ≤ n →
      480 * ((n : ℤ) + 1) * a n +
        30 * (-32 * (n : ℤ) ^ 2 - 14821 * (n : ℤ) + 42287) * a (n - 1) +
        (878700 * (n : ℤ) ^ 2 - 403433 * (n : ℤ) + 5134227) * a (n - 2) +
        (911423 * (n : ℤ) - 656446) * (2 * (n : ℤ) - 3) * a (n - 3) = 0)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 3 ≤ n →
      ((n : ℤ) - 2) * (20 * (n : ℤ) ^ 2 - 5 * (n : ℤ) - 3) * a n -
        (n : ℤ) * (2 * (n : ℤ) + 1) * (20 * (n : ℤ) ^ 2 + 35 * (n : ℤ) + 12) * a (n - 1) = 0)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a001784.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a001784_R1
