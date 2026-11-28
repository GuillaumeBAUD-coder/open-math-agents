import OMAStatements.S_oeis_a233567

-- Reduction oeis-a233567.R1 of oeis-a233567: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a233567_R1

open OMA.S_oeis_a233567

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 2 < n → n ≠ 5 → (∃ p q : ℕ, 0 < q ∧ p.Prime ∧ p + q = n ∧ (p ^ 4 + Nat.totient q ^ 4).Prime)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 2 < n → n ≠ 5 → ∃ p : ℕ, p.Prime ∧ p < n ∧ (p ^ 2 + Nat.totient (n - p) ^ 2).Prime

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a233567.main := by
  intro h1 h2 x1 x2 x3
  exact ⟨h1 x1 x2 x3, h2 x1 x2 x3⟩

end OMA.R_oeis_a233567_R1
