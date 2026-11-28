import OMAStatements.S_mo_275818

-- Reduction mo-275818.R1 of mo-275818: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_mo_275818_R1

open OMA.S_mo_275818
open Matrix Finset

/-- Step H1 of the reduction. -/
def H1 : Prop := (admissible witness ∧ witness.rank = 1 ∧
      ∃ U V U' : Mat, ∃ s : Fin 2 → ℝ, svd witness U V s ∧ svd witness U' V s ∧
        (U*Vᵀ).trace=0 ∧ (U'*Vᵀ).trace=8/5)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ (A U V : Mat) (s : Fin 2 → ℝ), admissible A → A.det ≠ 0 → svd A U V s →
      (U*Vᵀ).trace = 2*A.trace/Real.sqrt (A.trace^2+(A 1 0-A 0 1)^2) ∧
      Real.sqrt 2 < (U*Vᵀ).trace)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ ε : ℝ, 0 < ε → ∃ (A U V : Mat) (s : Fin 2 → ℝ),
      admissible A ∧ strict A ∧ A.det ≠ 0 ∧ svd A U V s ∧ (U*Vᵀ).trace < Real.sqrt 2+ε)

theorem main : H1 → H2 → H3 → type_of% @OMA.S_mo_275818.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_mo_275818_R1
