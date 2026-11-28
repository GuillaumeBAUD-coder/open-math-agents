import OMAStatements.S_oeis_a248366

-- Reduction oeis-a248366.R1 of oeis-a248366: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a248366_R1

open OMA.S_oeis_a248366

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ prime (m + n) - prime m ∣ m + n)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 0 < n → ((∃ m : ℕ, 0 < m ∧ m ≤ n ^ 2 ∧ prime (m + n) - prime m ∣ m + n) ↔
        n ∉ ({5, 10, 15, 27} : Finset ℕ))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a248366.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a248366_R1
