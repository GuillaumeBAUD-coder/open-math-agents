import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2
import Mathlib

-- Reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R1 of step
-- Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3
-- Credit: @zangetsu787

/-
Reduction of the summability for every length at least five to two smaller statements:

H1 is the base case k = 5 alone.  H2 is the monotonicity of the extremal number in the
length: a set with no 5-term progression has no k-term progression for any k >= 6, since a
k-term progression contains its first five terms as a 5-term progression.  Consequently the
normalized k-term densities are dominated termwise by the normalized 5-term densities, and
the comparison test gives the result for every k >= 5.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R1

open Erdos142 Filter

/-- The normalized 5-term extremal densities on the scales 4^j are summable. -/
def H1 : Prop := Summable (fun j : ℕ ↦ (r 5 (4 ^ j) : ℝ) / (4 : ℝ) ^ j)

/-- For every length k at least six the k-term extremal number at any scale is at most the
5-term extremal number at that scale. -/
def H2 : Prop := ∀ k : ℕ, 6 ≤ k → ∀ N : ℕ, r k N ≤ r 5 N

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2.H3 := by
  intro h5 hmono k hk
  have hle : ∀ j : ℕ, (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j ≤
      (r 5 (4 ^ j) : ℝ) / (4 : ℝ) ^ j := by
    intro j
    by_cases h : k = 5
    · subst k
      rfl
    · have hk6 : 6 ≤ k := by omega
      exact div_le_div_of_nonneg_right (by exact_mod_cast hmono k hk6 (4 ^ j)) (by positivity)
  have hnonneg : ∀ j : ℕ, 0 ≤ (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j := by
    intro j
    positivity
  exact Summable.of_nonneg_of_le hnonneg hle h5

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R1
