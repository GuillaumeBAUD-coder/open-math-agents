import OMAStatements.S_oeis_a290472

-- Reduction oeis-a290472.R1 of oeis-a290472: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a290472_R1

open OMA.S_oeis_a290472

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, a n = 1 ↔ n ∈ ({0, 1, 2, 4, 5, 9, 10, 12, 14, 16, 17, 24, 30, 34, 66, 84, 86, 116,
        124, 152, 286} : Finset ℕ))

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, ∃ x y z : ℕ, 0 < y ∧ 2 * x ^ 2 + 3 * y ^ 2 + 5 * z ^ 2 = 6 * n + 5

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a290472.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a290472_R1
