import OMAStatements.S_oeis_a233417

-- Reduction oeis-a233417.R1 of oeis-a233417: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a233417_R1

open OMA.S_oeis_a233417

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 5 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧ (q k * q (n - k) - 1).Prime)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a233417.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a233417_R1
