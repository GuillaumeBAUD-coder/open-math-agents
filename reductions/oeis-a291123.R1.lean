import OMAStatements.S_oeis_a291123

-- Reduction oeis-a291123.R1 of oeis-a291123: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a291123_R1

open OMA.S_oeis_a291123

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, a n = 1 ↔ n ∈ ({0, 3, 6, 23, 44} : Finset ℕ))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ m : ℕ, 0 < m → Nat.Coprime m 6 →
        ∃ p q r : ℕ, p.Prime ∧ (p - 1) ^ 2 + q ^ 2 + 3 * r ^ 2 = m)

/-- Step H4 of the reduction. -/
def H4 : Prop := ( (∀ n : ℕ, ∃ x y z : ℕ, (x + y + 2 * z).Prime ∧ x ^ 2 + y ^ 2 + z ^ 2 = 4 * n + 1) ∧ (∀ n : ℕ, ∃ x y z : ℕ, (x + 3 * y).Prime ∧ x ^ 2 + y ^ 2 + z ^ 2 = 4 * n + 2) ∧ ∀ n : ℕ, ∃ x y z : ℕ, (2 * x + 1).Prime ∧ 2 * x ^ 2 + y ^ 2 + z ^ 2 = 4 * n + 3 )

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a291123.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a291123_R1
