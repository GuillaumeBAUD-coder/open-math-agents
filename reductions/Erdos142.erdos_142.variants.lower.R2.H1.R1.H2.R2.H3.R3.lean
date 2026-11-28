import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2
import Mathlib

-- Reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R3 of step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3
-- Credit: @0xf905

/-!
# Summable 4-adic extremal densities from the sharp logarithmic iterated-log threshold

The target is step H3 of reduction R2.H1.R1.H2.R2 of Erdős 142: for every progression length
k at least five, the normalized 4-adic extremal numbers r_k(4^j) / 4^j are summable.

Rather than demanding a stretched-exponential or power-of-log saving (which are strictly stronger
than needed for summability), this reduction isolates the classical Erdős-Turán summability
boundary:

  H1: for every k ≥ 5, r_k(N) / N ≤ C / (log N * (log log N)^(1 + ε)) eventually.
  H2: for every ε > 0, the Bertrand-type series ∑ (j * (log (j * log 4))^(1 + ε))⁻¹ converges
      (provable independently by Cauchy condensation).

Specializing H1 to N = 4^j gives log(4^j) = j * log 4, and factoring out C / log 4 reduces H3
directly to H2 via comparison.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3

open Erdos142 Filter

/-- For every progression length at least five, the extremal density eventually decays at the
logarithmic iterated-log summability threshold. -/
def H1 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
    ∀ᶠ N : ℕ in atTop,
      (r k N : ℝ) / (N : ℝ) ≤
        C / (Real.log (N : ℝ) * (Real.log (Real.log (N : ℝ))) ^ (1 + ε))

/-- The corresponding Bertrand-type series at the 4-adic scales is summable for every ε > 0. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Summable (fun j : ℕ ↦
      ((j : ℝ) * (Real.log ((j : ℝ) * Real.log 4)) ^ (1 + ε))⁻¹)

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2.H3 := by
  intro h1 h2 k hk
  obtain ⟨C, ε, hC, hε, hb⟩ := h1 k hk
  have hs : Summable (fun j : ℕ ↦
      (C / Real.log 4) * ((j : ℝ) * (Real.log ((j : ℝ) * Real.log 4)) ^ (1 + ε))⁻¹) :=
    (h2 ε hε).mul_left (C / Real.log 4)
  have hT : Tendsto (fun j : ℕ ↦ (4 : ℕ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat hs ?_
  filter_upwards [hT.eventually hb] with j hj
  rw [Real.norm_of_nonneg (by positivity)]
  have hx : ((4 ^ j : ℕ) : ℝ) = (4 : ℝ) ^ j := by norm_num
  have hL : Real.log ((4 ^ j : ℕ) : ℝ) = (j : ℝ) * Real.log 4 := by
    rw [hx, Real.log_pow]
  rw [hL, hx] at hj
  calc (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j
      ≤ C / ((j : ℝ) * Real.log 4 * (Real.log ((j : ℝ) * Real.log 4)) ^ (1 + ε)) := hj
    _ = (C / Real.log 4) * ((j : ℝ) * (Real.log ((j : ℝ) * Real.log 4)) ^ (1 + ε))⁻¹ := by
        simp only [div_eq_mul_inv, mul_inv]
        ring

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3
