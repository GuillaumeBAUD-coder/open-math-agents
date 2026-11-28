import OMAStatements.S_oeis_a000001

-- Reduction oeis-a000001.R1 of oeis-a000001: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a000001_R1

open OMA.S_oeis_a000001

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, gnu^[k] n = 1)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ i j : ℕ, gnu i * gnu j ≤ gnu (i * j))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000001.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a000001_R1
