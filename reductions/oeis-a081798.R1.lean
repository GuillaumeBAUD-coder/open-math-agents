import OMAStatements.S_oeis_a081798

-- Reduction oeis-a081798.R1 of oeis-a081798: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a081798_R1

open OMA.S_oeis_a081798

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 3 ≤ n →
      (n : ℤ) ^ 2 * (3 * n - 4) * a n
        - (3 * (n : ℤ) - 2) * (30 * (n : ℤ) ^ 2 - 50 * n + 13) * a (n - 1)
        + (9 * (n : ℤ) ^ 3 - 30 * (n : ℤ) ^ 2 + 29 * n - 6) * a (n - 2)
        - (3 * (n : ℤ) - 1) * ((n : ℤ) - 2) ^ 2 * a (n - 3) = 0)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 4 ≤ n →
      (n : ℤ) ^ 2 * a n
        + (-28 * (n : ℤ) ^ 2 + 24 * n - 3) * a (n - 1)
        + 3 * (-19 * (n : ℤ) ^ 2 + 78 * n - 77) * a (n - 2)
        + (5 * (n : ℤ) - 12) * ((n : ℤ) - 3) * a (n - 3)
        - 2 * ((n : ℤ) - 3) ^ 2 * a (n - 4) = 0)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a081798.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a081798_R1
