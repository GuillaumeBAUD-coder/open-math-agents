import OMAStatements.S_mo_220800

-- Reduction mo-220800.R1 of mo-220800: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_mo_220800_R1

open OMA.S_mo_220800
open MeasureTheory

/-- Step H1 of the reduction. -/
def H1 : Prop := (∃ μ : Measure ℝ, standard μ ∧ ∀ c : ℝ, 0<c →
      Real.exp (-c) < (μ.prod μ).real {v | |v.1| ≤ |v.1+v.2|+1})

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n (t : ℝ), 1 ≤ t →
      (∀ μ ν : Measure ℝ, standard μ → standard ν → dropProb μ ν n t ≤ 2*rate n t) ∧
      (∃ μ ν : Measure ℝ, standard μ ∧ standard ν ∧ rate n t/24 ≤ dropProb μ ν n t))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∃ μ : Measure ℝ, standard μ ∧ μ.map Neg.neg=μ ∧
      (∀ k : ℕ, 1/(16*((2:ℝ)^k)^6) ≤ oneDrop μ (2^k)) ∧
      ∀ c : ℝ, 0<c → ∃ t : ℝ, 1 ≤ t ∧ Real.exp (-c*t^2) < oneDrop μ t)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_mo_220800.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_mo_220800_R1
