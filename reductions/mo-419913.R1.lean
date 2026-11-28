import OMAStatements.S_mo_419913

-- Reduction mo-419913.R1 of mo-419913: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_mo_419913_R1

open OMA.S_mo_419913
open scoped ENNReal

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], ∃ B BT : Space p →L[ℝ] Space p,
      extendsAt bAct p B ∧ extendsAt btAct p BT)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ B BT : Space 2 →L[ℝ] Space 2, extendsAt bAct 2 B → extendsAt btAct 2 BT →
      ∀ f g : Space 2, inner ℝ (B f) g = inner ℝ f (BT g))

/-- Step H3 of the reduction. -/
def H3 : Prop := Function.Bijective bAct

/-- Step H4 of the reduction. -/
def H4 : Prop := ( Function.Bijective btAct ∧ (∃ x : Space ⊤, x ≠ 0 ∧ ∀ i : I,
      (1/2 : ℝ)*x i + (1-1/2 : ℝ)*btAct (bAct (fun j => x j)) i = 0) )

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_mo_419913.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_mo_419913_R1
