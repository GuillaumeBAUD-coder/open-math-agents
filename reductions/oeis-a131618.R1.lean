import OMAStatements.S_oeis_a131618

-- Reduction oeis-a131618.R1 of oeis-a131618: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a131618_R1

open OMA.S_oeis_a131618

/-- Step H1 of the reduction. -/
def H1 : Prop := (¬ 4 ∈ Nat.digits 10 (3 ^ 106))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ k : ℕ, 106 < k → 4 ∈ Nat.digits 10 (3 ^ k)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a131618.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a131618_R1
