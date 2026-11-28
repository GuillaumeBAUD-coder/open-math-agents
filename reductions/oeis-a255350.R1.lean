import OMAStatements.S_oeis_a255350

-- Reduction oeis-a255350.R1 of oeis-a255350: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a255350_R1

open OMA.S_oeis_a255350

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, ∃ a b c d : ℕ,
        n = a * (2 * a - 1) + b * (2 * b - 1) + c * (2 * c + 1) + d * (2 * d + 1))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, ∃ w x y z : ℕ,
        n = w * (3 * w - 1) / 2 + x * (3 * x - 1) / 2 + y * (3 * y + 1) / 2 + z * (3 * z + 1) / 2)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a255350.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a255350_R1
