import OMAStatements.S_oeis_a299537

-- Reduction oeis-a299537.R1 of oeis-a299537: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a299537_R1

open OMA.S_oeis_a299537
open Classical

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 0 < n → (a n = 1 ↔ ∃ k : ℕ, ∃ m ∈ ({1, 2, 3, 5, 7, 11, 15, 19, 43, 47, 135, 1103} :
        Finset ℕ), n = 4 ^ k * m))

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, 1 < n → ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ^ 2 ∧
        (IsPow4 (2 * x) ∨ IsPow4 (2 * y)) ∧ IsPow4 (2 * (x + 3 * y))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a299537.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a299537_R1
