import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1

/-!
# Step H2 of Erdos142 lower.R2.H1.R1: summable extremal densities

The merged parent proves the glue that turns a pointwise density bound into the summability
of the extremal densities on the geometric scales. This reduction isolates the genuinely open
quantitative input as a polynomial saving along those scales; the comparison series is a
standard p-series already proved in the library.
-/

-- Reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R3 of step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted.

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3

open Erdos142 Filter Real

/-- Open quantitative core: a fixed polynomial saving for every progression length at least four. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ j : ℕ, (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j ≤
      C * (((j + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)))

/-- Library-proved p-series: the exponent greater than one makes the majorant summable. -/
def H2 : Prop :=
  Summable (fun j : ℕ ↦ (((j + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))))

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1.H2 := by
  intro hpt hp k hk
  obtain ⟨C, hC, hb⟩ := hpt k hk
  have hs : Summable (fun j : ℕ ↦ C * ((((j + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))))) := hp.mul_left C
  refine Summable.of_nonneg_of_le (fun j ↦ by positivity) ?_ hs
  intro j
  exact hb j

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3
