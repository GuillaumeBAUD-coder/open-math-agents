import OMAStatements.S_oeis_a258803

-- Reduction oeis-a258803.R1 of oeis-a258803: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a258803_R1

open OMA.S_oeis_a258803

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
        Nat.nth Nat.Prime (q - 1) - 1 = n * (Nat.nth Nat.Prime (p - 1) - 1))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ s t : ℤ, (s = 1 ∨ s = -1) → (t = 1 ∨ t = -1) → ∀ r : ℚ, 0 < r →
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
          r = ((Nat.nth Nat.Prime (p - 1) : ℚ) + s) / ((Nat.nth Nat.Prime (q - 1) : ℚ) + t)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a258803.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a258803_R1
