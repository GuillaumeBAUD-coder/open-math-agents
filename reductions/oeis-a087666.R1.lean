import OMAStatements.S_oeis_a087666

-- Reduction oeis-a087666.R1 of oeis-a087666: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a087666_R1

open OMA.S_oeis_a087666

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 6 ≤ n → ∃ k : ℕ, (b n k).den = 1)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 6 ≤ n →
      |(∑ m ∈ Finset.Icc 6 n, (a m : ℝ)) - 2 * (n : ℝ)| ≤ C * Real.sqrt (n : ℝ))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a087666.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a087666_R1
