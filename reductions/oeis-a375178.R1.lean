import OMAStatements.S_oeis_a375178

-- Reduction oeis-a375178.R1 of oeis-a375178: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a375178_R1

open OMA.S_oeis_a375178

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ p : ℕ, p.Prime → 7 ≤ p → (p : ℤ) ^ 5 ∣ a p - 1)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ p r : ℕ, p.Prime → 5 ≤ p → 2 ≤ r → (p : ℤ) ^ (3 * r + 3) ∣ a (p ^ r) - a (p ^ (r - 1))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a375178.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a375178_R1
