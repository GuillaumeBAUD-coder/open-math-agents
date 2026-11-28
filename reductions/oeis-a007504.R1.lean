import OMAStatements.S_oeis_a007504

-- Reduction oeis-a007504.R1 of oeis-a007504: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a007504_R1

open OMA.S_oeis_a007504

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 5340 ≤ n →
      ∃ i j k : ℕ, 0 < i ∧ 0 < j ∧ 0 < k ∧ n = a i + a j + 2 * a k)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 16866 < n →
      ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ n = p + a k)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 13392 < n →
      ∃ q k : ℕ, IsPractical q ∧ 0 < k ∧ n = q + a k)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a007504.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a007504_R1
