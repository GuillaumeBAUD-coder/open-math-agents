import OMAStatements.S_oeis_a210394

-- Reduction oeis-a210394.R1 of oeis-a210394: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a210394_R1

open OMA.S_oeis_a210394

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n m : ℕ, 0 < n → IsLeast {m : ℕ | IsAdmissible n m} m → Nat.Prime m

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n m : ℕ, 0 < n → IsLeast {m : ℕ | IsAdmissible n m} m → m ≤ S n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a210394.main := by
  intro h1 h2 x1 x2 x3 x4
  exact ⟨h1 x1 x2 x3 x4, h2 x1 x2 x3 x4⟩

end OMA.R_oeis_a210394_R1
