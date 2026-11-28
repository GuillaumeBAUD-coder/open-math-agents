import OMAStatements.S_oeis_a375786

-- Reduction oeis-a375786.R1 of oeis-a375786: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a375786_R1

open OMA.S_oeis_a375786

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 0 < n → (∃ a b c : ℕ, admissible n a b c ∧ leastSides n a b)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 0 < n → (∀ a b c : ℕ, admissible n a b c → leastSides n a b →
      ∀ x y z : ℕ, admissible n x y z → a*b*c ≤ x*y*z)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a375786.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a375786_R1
