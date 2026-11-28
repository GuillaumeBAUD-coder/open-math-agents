import OMAStatements.S_opg_fractional_hadwiger

-- Reduction opg-fractional-hadwiger.R1 of opg-fractional-hadwiger: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_opg_fractional_hadwiger_R1

open OMA.S_opg_fractional_hadwiger

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), chif G ≤ (had G : ℝ)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), chi G ≤ hadf G

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), chif G ≤ hadf G

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_opg_fractional_hadwiger.main := by
  intro h1 h2 h3 x1 x2 x3 x4
  exact ⟨h1 x1 x4, h2 x1 x4, h3 x1 x4⟩

end OMA.R_opg_fractional_hadwiger_R1
