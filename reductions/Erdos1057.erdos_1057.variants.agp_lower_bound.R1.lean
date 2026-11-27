import FormalConjectures.ErdosProblems.«1057»
import Mathlib

/-! The Alford-Granville-Pomerance lower bound for the Carmichael counting function from
Harman's improvement. Harman, Watt's mean value theorem and Carmichael numbers, Int. J.
Number Theory 4 (2008), proves C(x) > x^0.33336704 for large x. Since 2/7 is smaller than
0.33336704, the power x^(2/7) is at most x^0.33336704 once x ≥ 1. -/

namespace OMA.R_Erdos1057_erdos_1057_variants_agp_lower_bound_R1
open Filter

/-- Harman's lower bound for the Carmichael counting function. -/
def H1 : Prop := ∀ᶠ x in atTop, Erdos1057.carmichaelCounting x > x ^ (0.33336704 : ℝ)

/-- Comparison of the two powers for large x. -/
def H2 : Prop := ∀ᶠ x : ℝ in atTop, x ^ (2 / 7 : ℝ) ≤ x ^ (0.33336704 : ℝ)

theorem main : H1 → H2 → type_of% @Erdos1057.erdos_1057.variants.agp_lower_bound := by
  intro hharman hcomp
  filter_upwards [hharman, hcomp] with x h1 h2
  exact lt_of_le_of_lt h2 h1

end OMA.R_Erdos1057_erdos_1057_variants_agp_lower_bound_R1
