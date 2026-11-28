import OMAStatements.S_oeis_a261437

-- Reduction oeis-a261437.R1 of oeis-a261437: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a261437_R1

open OMA.S_oeis_a261437

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → ∀ r : ℤ, Int.gcd n r = 1 →
        {k : ℕ | 0 < k ∧ IsPrimeIndexedPrime ((k : ℤ) * n + r)}.Infinite)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ r : ℤ, (r = 1 ∨ r = -1) → ∀ n : ℕ, 0 < n →
        ∃ k : ℕ, 0 < k ∧ IsPrimeIndexedPrime ((k : ℤ) * n + r) ∧
          IsPrimeIndexedPrime ((k : ℤ) ^ 2 * n + 1)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a261437.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a261437_R1
