import OMAStatements.S_mo_302095

-- Reduction mo-302095.R1 of mo-302095: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_mo_302095_R1

open OMA.S_mo_302095
open ArithmeticFunction

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 1 ≤ n → (Matrix.of fun i j : Fin n => moebius (i.val + j.val + 1)).det ≠ 0

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → (Matrix.of fun i j : Fin n => moebius (i.val + j.val + 2) ^ 2).det ≠ 0

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_mo_302095.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_mo_302095_R1
