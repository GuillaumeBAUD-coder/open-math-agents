import OMAStatements.S_oeis_a005234

-- Reduction oeis-a005234.R1 of oeis-a005234: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a005234_R1

open OMA.S_oeis_a005234
open Real

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ p : ℕ, p.Prime → (primorial p + 1).Prime →
      ∃ q : ℕ, q.Prime ∧ primorial p + 1 < q ∧ (q : ℝ) < (primorial p : ℝ) + exp 1 * p)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ p : ℕ, p.Prime → (primorial p + 1).Prime →
      ∃ q : ℕ, q.Prime ∧ primorial p + 1 < q ∧ q < primorial p + p ^ 2)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a005234.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a005234_R1
