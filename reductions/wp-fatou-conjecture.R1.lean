import OMAStatements.S_wp_fatou_conjecture

-- Reduction wp-fatou-conjecture.R1 of wp-fatou-conjecture: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_wp_fatou_conjecture_R1

open OMA.S_wp_fatou_conjecture
open Filter Topology Bornology

/-- Step H1 of the reduction. -/
def H1 : Prop := IsOpen {c : ℂ | IsHyperbolicParam c}

/-- Step H2 of the reduction. -/
def H2 : Prop := Dense {c : ℂ | IsHyperbolicParam c}

theorem main : H1 → H2 → type_of% @OMA.S_wp_fatou_conjecture.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_wp_fatou_conjecture_R1
