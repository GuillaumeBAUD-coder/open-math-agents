import OMAStatements.S_arxiv_2209_09843

-- Reduction arxiv-2209.09843.R1 of arxiv-2209.09843: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_arxiv_2209_09843_R1

open OMA.S_arxiv_2209_09843
open Polynomial

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ P Q : ℝ[X], P.Monic → Q.Monic → (∀ i, 0 ≤ P.coeff i) → (∀ i, 0 ≤ Q.coeff i) →
      ZeroOne (P * Q) → ZeroOne P

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ P Q : ℝ[X], P.Monic → Q.Monic → (∀ i, 0 ≤ P.coeff i) → (∀ i, 0 ≤ Q.coeff i) →
      ZeroOne (P * Q) → ZeroOne Q

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_arxiv_2209_09843.main := by
  intro h1 h2 x1 x2 x3 x4 x5 x6 x7
  exact ⟨h1 x1 x2 x3 x4 x5 x6 x7, h2 x1 x2 x3 x4 x5 x6 x7⟩

end OMA.R_arxiv_2209_09843_R1
