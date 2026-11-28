import OMAStatements.S_oeis_a361717

-- Reduction oeis-a361717.R1 of oeis-a361717: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a361717_R1

open OMA.S_oeis_a361717

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ p : ℕ, p.Prime → 5 ≤ p → ((p : ℤ) ^ 4) ∣ a p)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ p : ℕ, p.Prime → p ≠ 3 →
      ((p : ℤ) ^ 3) ∣ (a (p - 1) - (1 - 2 * (p : ℤ) - (p : ℤ) ^ 2)))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a361717.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a361717_R1
