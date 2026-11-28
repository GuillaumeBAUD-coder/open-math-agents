import OMAStatements.S_mo_376777

-- Reduction mo-376777.R1 of mo-376777: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_mo_376777_R1

open OMA.S_mo_376777
open ArithmeticFunction

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ m n : ℕ, 0 < m → 0 < n →
      Nat.totient (m ^ 2) * sigma 1 (m ^ 2) = Nat.totient (n ^ 2) * sigma 1 (n ^ 2) → m = n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ m n : ℕ, 0 < m → 0 < n →
      (sigma 1 (m ^ 2) : ℚ) / (Nat.totient (m ^ 2) : ℚ) =
        (sigma 1 (n ^ 2) : ℚ) / (Nat.totient (n ^ 2) : ℚ) → m = n)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_mo_376777.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_mo_376777_R1
