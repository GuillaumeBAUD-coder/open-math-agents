import OMAStatements.S_oeis_a178808

-- Reduction oeis-a178808.R1 of oeis-a178808: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a178808_R1

open OMA.S_oeis_a178808

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → n ^ 2 ∣ S n)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ p : ℕ, p.Prime → 3 < p →
        let q : ℤ := ((2 ^ (p - 1) - 1) / p : ℕ)
        (p : ℤ) ^ 5 ∣ (S p : ℤ) - (p ^ 2 - 4 * p ^ 3 * q - 2 * p ^ 4 * q ^ 2)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a178808.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a178808_R1
