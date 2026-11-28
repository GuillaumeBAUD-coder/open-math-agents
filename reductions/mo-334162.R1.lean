import OMAStatements.S_mo_334162

-- Reduction mo-334162.R1 of mo-334162: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_mo_334162_R1

open OMA.S_mo_334162
open MeasureTheory Metric

/-- Step H1 of the reduction. -/
def H1 : Prop := (∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 0 < d → weakBound d C)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∃ A : ℝ, 0 < A ∧ ∃ k : ℕ, ∀ d : ℕ, 0 < d → weakBound d (A * (d : ℝ) ^ k))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_mo_334162.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_mo_334162_R1
