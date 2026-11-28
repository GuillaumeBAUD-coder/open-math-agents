import OMAStatements.S_oeis_a239328

-- Reduction oeis-a239328.R1 of oeis-a239328: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a239328_R1

open OMA.S_oeis_a239328

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 3 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 4 < n → ∃ p < n, Nat.Prime p ∧
      (Nat.primeCounting ((p + 1) * n) - Nat.primeCounting (p * n)).Prime)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a239328.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a239328_R1
