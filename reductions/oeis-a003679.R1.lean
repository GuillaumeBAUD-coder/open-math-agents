import OMAStatements.S_oeis_a003679
import Mathlib

-- Reduction oeis-a003679.R1 of A003679: Numbers that are not the sum of 3 pentagonal numbers.
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a003679_R1

open OMA.S_oeis_a003679

/-- The infinite half of Guy's conjecture: every integer above the claimed largest exception
`33066` is a sum of three pentagonal numbers. -/
def H1 : Prop := ∀ n : ℕ, 33066 < n → ∃ a b c : ℕ, n = pent a + pent b + pent c

/-- The finite half: below the bound there are exactly 210 integers that are not a sum of three
pentagonal numbers. This is a finite computation (66 times 33067 cases at most). -/
def H2 : Prop :=
  {n : ℕ | n ≤ 33066 ∧ ¬ ∃ a b c : ℕ, n = pent a + pent b + pent c}.ncard = 210

/-- The witness that the bound is attained: `33066` is itself not a sum of three pentagonal
numbers (a single decidable computation). -/
def H3 : Prop := 33066 ∈ NotSum3

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a003679.main := by
  intro h1 h2 h3
  have hset : NotSum3 =
      {n : ℕ | n ≤ 33066 ∧ ¬ ∃ a b c : ℕ, n = pent a + pent b + pent c} := by
    ext n
    constructor
    · intro hn
      refine ⟨?_, hn⟩
      by_contra hgt
      exact hn (h1 n (Nat.lt_of_not_le hgt))
    · rintro ⟨-, hn⟩
      exact hn
  refine ⟨?_, ?_, h3, ?_⟩
  · rw [hset]
    exact h2
  · rw [hset]
    exact (Set.finite_Iic 33066).subset (by intro n hn; exact hn.1)
  · intro n hn
    by_contra hgt
    exact hn (h1 n (Nat.lt_of_not_le hgt))

end OMA.R_oeis_a003679_R1
