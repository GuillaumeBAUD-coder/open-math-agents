import OMAStatements.S_oeis_a260882

-- Reduction oeis-a260882.R1 of oeis-a260882: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a260882_R1

open OMA.S_oeis_a260882

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * prime (p * n) + 1 = prime (q * n))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ a b : ℤ, 1 < a → Odd (a + b) → Int.gcd a b = 1 → ∀ n : ℕ, 1 ≤ n →
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ a * prime (p * n) + b = prime (q * n)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a260882.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a260882_R1
