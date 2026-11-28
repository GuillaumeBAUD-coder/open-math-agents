import OMAStatements.S_oeis_a234514

-- Reduction oeis-a234514.R1 of oeis-a234514: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a234514_R1

open OMA.S_oeis_a234514
open Classical in

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 12 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 4 < n → ∃ p : ℕ, p.Prime ∧ p < n - 2 ∧
      (q (p + Nat.totient (n - p) / 2) + 1).Prime)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a234514.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a234514_R1
