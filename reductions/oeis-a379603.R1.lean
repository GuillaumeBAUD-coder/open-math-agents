import OMAStatements.S_oeis_a379603

-- Reduction oeis-a379603.R1 of oeis-a379603: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a379603_R1

open OMA.S_oeis_a379603

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 5≤n → largest (2*n) (evenValue n)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 5≤n → largest (2*n+1) (10*evenValue n+6)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a379603.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a379603_R1
