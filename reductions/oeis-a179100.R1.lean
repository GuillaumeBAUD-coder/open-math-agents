import OMAStatements.S_oeis_a179100

-- Reduction oeis-a179100.R1 of oeis-a179100: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a179100_R1

open OMA.S_oeis_a179100

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → (n : ℤ) ∣ S n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ p : ℕ, p.Prime → (p : ℤ) ∣ a p - 3 * jacobiSym (p : ℤ) 3)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a179100.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a179100_R1
