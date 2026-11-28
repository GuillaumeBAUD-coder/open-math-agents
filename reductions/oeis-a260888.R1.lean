import OMAStatements.S_oeis_a260888

-- Reduction oeis-a260888.R1 of oeis-a260888: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a260888_R1

open OMA.S_oeis_a260888

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
        2 + 3 * Nat.primeCounting (p * n) = 4 * Nat.primeCounting (q * n))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b → ∀ c : ℤ, ∀ n : ℕ, 1 ≤ n →
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
          (a : ℤ) * Nat.primeCounting (p * n) - b * Nat.primeCounting (q * n) = c

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a260888.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a260888_R1
