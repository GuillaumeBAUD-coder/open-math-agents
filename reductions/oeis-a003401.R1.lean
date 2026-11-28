import OMAStatements.S_oeis_a003401

-- Reduction oeis-a003401.R1 of oeis-a003401: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a003401_R1

open OMA.S_oeis_a003401

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ k : ℕ, 5 ≤ k → ¬ (F k).Prime) → HasSum (fun n : {n : ℕ // InA003401 n} => (1 : ℝ) / (n : ℕ))
        (2 * ∏ k ∈ Finset.range 5, (1 + 1 / (F k : ℝ)))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ k : ℕ, 5 ≤ k → ¬ (F k).Prime) → 2 * ∏ k ∈ Finset.range 5, (1 + 1 / (F k : ℝ)) = 4869735552 / 1431655765

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a003401.main := by
  intro h1 h2 x1
  exact ⟨h1 x1, h2 x1⟩

end OMA.R_oeis_a003401_R1
