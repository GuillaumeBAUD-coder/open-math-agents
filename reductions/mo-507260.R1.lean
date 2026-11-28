import OMAStatements.S_mo_507260

-- Reduction mo-507260.R1 of mo-507260: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_mo_507260_R1

open OMA.S_mo_507260

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ s : ℕ, 1 ≤ s → discreteBound (2*s-1) (4*s+1) alternating (4^s) ∧
      (∃ L, extensionBound (2*s-1) (4*s+1) alternating L) ∧
      ∀ L, extensionBound (2*s-1) (4*s+1) alternating L → (16/3:ℝ)^s ≤ L)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ C : ℝ, 1 < C → ∃ (k n : ℕ) (z : ℕ → ℝ) (D ε : ℝ),
      k+2 ≤ n ∧ 0 < D ∧ 0 < ε ∧ discreteBound k n z D ∧
      (∃ L, extensionBound k n z L) ∧ ∀ L, extensionBound k n z L → C*D+ε ≤ L

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_mo_507260.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_mo_507260_R1
