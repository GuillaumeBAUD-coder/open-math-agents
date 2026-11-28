import OMAStatements.S_oeis_a187563

-- Reduction oeis-a187563.R1 of oeis-a187563: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a187563_R1

open OMA.S_oeis_a187563

/-- Step H1 of the reduction. -/
def H1 : Prop := {p : ℕ | p.Prime ∧ ¬ ∃ k : ℕ, k < p ∧ (p * (p - k) - 1).Prime ∧ (p * (p - k) + 1).Prime} =
      {5, 11, 13, 31, 37, 53, 61, 73, 79, 97, 127}

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ p : ℕ, p.Prime → 3 ≤ p → ∃ q : ℕ, p < q ∧ q + 2 < p ^ 2 ∧ q.Prime ∧ (q + 2).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a187563.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a187563_R1
