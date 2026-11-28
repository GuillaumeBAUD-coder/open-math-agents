import OMAStatements.S_oeis_a064653

-- Reduction oeis-a064653.R1 of oeis-a064653: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a064653_R1

open OMA.S_oeis_a064653

/-- Step H1 of the reduction. -/
def H1 : Prop := {n : ℕ | 1 ≤ n ∧ ¬ IsRep n} =
        {1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 16, 18, 24, 26, 28, 36, 42, 60, 72, 84, 90, 96, 108, 240,
          300, 420, 1050, 1260}

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1260 < n →
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q * leastNonDivisorPrime n ^ 2

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a064653.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a064653_R1
