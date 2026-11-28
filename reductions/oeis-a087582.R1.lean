import OMAStatements.S_oeis_a087582

-- Reduction oeis-a087582.R1 of oeis-a087582: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a087582_R1

open OMA.S_oeis_a087582

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ m : ℕ, 1 ≤ m →
      ∃ p : ℕ, a m < p ∧ p.Prime ∧ IsPalindrome10 (p - a m) ∧ (p - a m) ∉ diffs (seqList m))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ d : ℕ, Even d → IsPalindrome10 d → ∃ m : ℕ, 1 ≤ m ∧ a (m + 1) - a m = d)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a087582.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a087582_R1
