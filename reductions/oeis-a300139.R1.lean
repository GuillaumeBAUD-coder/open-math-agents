import OMAStatements.S_oeis_a300139

-- Reduction oeis-a300139.R1 of oeis-a300139: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a300139_R1

open OMA.S_oeis_a300139
open Classical

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, a n = 1 ↔ ∃ k : ℕ, ∃ m ∈ ({0, 7, 8, 13, 22, 23, 24, 31, 44, 56, 71, 79, 88, 109, 120,
        152, 184, 472, 1912, 6008, 9080} : Finset ℕ), n = 16 ^ k * m)

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        (∃ s : ℤ, 3 * (x : ℤ) - y = 2 * s ^ 2) ∧ (IsSquare (5 * x) ∨ IsSquare y)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a300139.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a300139_R1
