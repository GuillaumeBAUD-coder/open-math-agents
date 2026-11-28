import OMAStatements.S_oeis_a305931

-- Reduction oeis-a305931.R1 of oeis-a305931: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a305931_R1

open OMA.S_oeis_a305931

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ k : ℕ, 68 < k → 0 ∈ Nat.digits 10 (3 ^ k))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, {k : ℕ | (Nat.digits 10 (3 ^ k)).count 0 = n}.Finite

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a305931.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a305931_R1
