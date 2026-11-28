import OMAStatements.S_mo_408352

-- Reduction mo-408352.R1 of mo-408352: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_mo_408352_R1

open OMA.S_mo_408352
open scoped BigOperators

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ (n : ℕ) (bits : ℕ → ZMod 2), evenParity (4 * n + 1) bits = 1 →
      reachable (4 * n + 1) bits)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ (n : ℕ) (bits : ℕ → ZMod 2), evenParity (4 * n + 3) bits = 0 →
      reachable (4 * n + 3) bits)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_mo_408352.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_mo_408352_R1
