import OMAStatements.S_oeis_a014689

-- Reduction oeis-a014689.R1 of oeis-a014689: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a014689_R1

open OMA.S_oeis_a014689

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ m : ℤ, 0 < m → ∀ r : ℤ, {n : ℕ | 0 < n ∧ Int.ModEq m (primeAt n - (n : ℤ)) r}.Infinite

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ m : ℤ, 0 < m → ∀ r : ℤ, {n : ℕ | 0 < n ∧ Int.ModEq m (primeAt n + (n : ℤ)) r}.Infinite

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a014689.main := by
  intro h1 h2 x1 x2 x3
  exact ⟨h1 x1 x2 x3, h2 x1 x2 x3⟩

end OMA.R_oeis_a014689_R1
