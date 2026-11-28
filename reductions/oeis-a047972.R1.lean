import OMAStatements.S_oeis_a047972

-- Reduction oeis-a047972.R1 of oeis-a047972: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a047972_R1

open OMA.S_oeis_a047972
open scoped Topology

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → (a n : ℝ) < Real.sqrt (primeAt n : ℝ))

/-- Step H2 of the reduction. -/
def H2 : Prop := Filter.Tendsto (fun n : ℕ => (a n : ℝ) / Real.sqrt (primeAt n : ℝ))
        Filter.atTop (𝓝 1)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a047972.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a047972_R1
