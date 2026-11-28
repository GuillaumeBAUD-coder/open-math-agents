import OMAStatements.S_oeis_a276045

-- Reduction oeis-a276045.R1 of oeis-a276045: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a276045_R1

open OMA.S_oeis_a276045

/-- Step H1 of the reduction. -/
def H1 : Prop := S.Infinite

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ q : ℕ, (q ∈ S ∧ q % 10 = 7) ↔ (q.Prime ∧ ∃ p : ℕ, p.Prime ∧ 2 * q + 1 = 5 * p))

/-- Step H3 of the reduction. -/
def H3 : Prop := {p : ℕ | p ∈ S ∧ p + 2 ∈ S}.Infinite

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a276045.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a276045_R1
