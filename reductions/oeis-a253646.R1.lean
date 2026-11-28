import OMAStatements.S_oeis_a253646

-- Reduction oeis-a253646.R1 of oeis-a253646: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a253646_R1

open OMA.S_oeis_a253646

/-- Step H1 of the reduction. -/
def H1 : Prop := {p : ℕ | p.Prime ∧ ∀ k : ℕ, 1 ≤ k → k ≤ 6 → Zeroless (p ^ k)}.Finite

/-- Step H2 of the reduction. -/
def H2 : Prop := {n : ℕ | ∀ k : ℕ, k ≤ 6 → Zeroless (n ^ k)}.Finite

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a253646.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a253646_R1
