import OMAStatements.S_oeis_a046927

-- Reduction oeis-a046927.R1 of oeis-a046927: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a046927_R1

open OMA.S_oeis_a046927

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 5 < n → Odd n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + 2 * q)

/-- Step H2 of the reduction. -/
def H2 : Prop := ({n : ℕ | Odd n ∧ ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → n = p + 2 * q →
        ¬ Nat.Prime (n + 2 * p) ∧ ¬ Nat.Prime (n + 2 * q)} = ({1, 3, 5, 59, 151} : Set ℕ))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a046927.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a046927_R1
