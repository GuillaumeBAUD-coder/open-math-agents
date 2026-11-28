import OMAStatements.S_oeis_a257109

-- Reduction oeis-a257109.R1 of oeis-a257109: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a257109_R1

open OMA.S_oeis_a257109

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, ¬ 3 ∣ n →
        ((∃ x y z : ℕ, Nat.gcd 3 x = 1 ∧ n = 3 * x ^ 2 + y ^ 2 + z ^ 2) ↔
          n ∉ ({1, 2, 10, 26, 31, 34, 47, 59, 166, 278, 451} : Finset ℕ)))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 14986 < n → ¬ 3 ∣ n → ∃ x y z : ℤ, (n : ℤ) = 3 * (3 * x) ^ 2 + y ^ 2 + z ^ 2

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a257109.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a257109_R1
