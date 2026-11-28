import OMAStatements.S_mo_453358

-- Reduction mo-453358.R1 of mo-453358: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_mo_453358_R1

open OMA.S_mo_453358
open Set Metric
open scoped ENat BigOperators

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ (X : Type) [MetricSpace X], (∀ M : ℕ, 1 ≤ M → coversByHalfBalls X M → doublingByPacking X (M^2))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ (X : Type) [MetricSpace X], (∀ (N : ℕ), doublingByPacking X N → ∀ k : ℕ, 1 ≤ k →
        ∀ x : X, ∀ r > 0, ∀ S : Set X, S ⊆ ball x r →
          distSeparated (r/(2:ℝ)^k) S → S.encard ≤ (N^k : ℕ))

theorem main : H1 → H2 → type_of% @OMA.S_mo_453358.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1, h2 x1⟩

end OMA.R_mo_453358_R1
