import OMAStatements.S_mo_343847

-- Reduction mo-343847.R1 of mo-343847: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_mo_343847_R1

open OMA.S_mo_343847

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → Odd p → (0 ≤ padicValRat p
        ((∑ k ∈ Finset.Icc 1 (p - 1), (franel (k - 1) : ℚ) / (k * 8 ^ (k - 1))
          - (-(p : ℚ) ^ 2 * bernoulli (p - 3))) / (p : ℚ) ^ 3))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ p : ℕ, p.Prime → Odd p → (0 ≤ padicValRat p
        ((∑ k ∈ Finset.Icc 1 (p - 1), (franel k : ℚ) / (k * 8 ^ k)
          - (3 * fermatQuotient p - 3 / 2 * p * fermatQuotient p ^ 2
              + (p : ℚ) ^ 2 * fermatQuotient p ^ 3)) / (p : ℚ) ^ 3))

theorem main : H1 → H2 → type_of% @OMA.S_mo_343847.main := by
  intro h1 h2 x1 x2 x3
  exact ⟨h1 x1 x2 x3, h2 x1 x2 x3⟩

end OMA.R_mo_343847_R1
