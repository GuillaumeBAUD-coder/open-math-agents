import OMAStatements.S_oeis_a237523

-- Reduction oeis-a237523.R1 of oeis-a237523: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a237523_R1

open OMA.S_oeis_a237523

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 7 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, a n = 1 ↔ n = 8 ∨ n = 9 ∨ n = 13 ∨ n = 15 ∨ n = 20 ∨ n = 132)

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, 5 < n → n ≠ 10 → n ≠ 15 → n ≠ 20 → n ≠ 60 → n ≠ 105 →
        ∃ k, 0 < k ∧ 2 * k < n ∧ IsSquare (Nat.totient (k * (n - k)))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a237523.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a237523_R1
