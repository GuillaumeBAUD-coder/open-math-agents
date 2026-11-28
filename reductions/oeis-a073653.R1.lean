import OMAStatements.S_oeis_a073653

-- Reduction oeis-a073653.R1 of oeis-a073653: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a073653_R1

open OMA.S_oeis_a073653
open Filter Topology

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ p : ℕ, Nat.Prime p → Odd p → ∃ n : ℕ, a n = p)

/-- Step H2 of the reduction. -/
def H2 : Prop := Tendsto (fun n : ℕ => (a n : ℝ) / (Nat.nth Nat.Prime n : ℝ)) atTop (𝓝 1)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a073653.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a073653_R1
