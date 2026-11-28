import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3
import Mathlib

/-!
Summability of the Bertrand-type series `sum over j of (j * (log (j * log 4)) ^ (1 + eps))⁻¹`
(step H2 of reduction R3 of `Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3`).

Cauchy condensation (`summable_condensed_iff_of_nonneg`): the terms are nonnegative and antitone
from `j = 1` on (since `log 4 > 1`). The condensed term `2 ^ k * f (2 ^ k)` equals
`(log (2 ^ k * log 4)) ^ -(1 + eps)`, which is at most `(k * log 2) ^ -(1 + eps)`. That is a
convergent `p`-series with `p = 1 + eps > 1`.
-/

open Filter

theorem OMA.bertrand : ∀ ε : ℝ, 0 < ε →
    Summable (fun j : ℕ ↦
      ((j : ℝ) * (Real.log ((j : ℝ) * Real.log 4)) ^ (1 + ε))⁻¹) := by
  intro ε hε
  set L : ℝ := Real.log 4 with hLdef
  have hL1 : 1 < L := by
    rw [hLdef, Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 < L := by linarith
  have hlog_nonneg : ∀ j : ℕ, 0 ≤ Real.log ((j : ℝ) * L) := by
    intro j
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp
    · apply Real.log_nonneg
      have : (1 : ℝ) ≤ j := by exact_mod_cast h
      nlinarith
  set f : ℕ → ℝ := fun j ↦ ((j : ℝ) * (Real.log ((j : ℝ) * L)) ^ (1 + ε))⁻¹ with hf
  have hnn : ∀ n, 0 ≤ f n := by
    intro n
    have := hlog_nonneg n
    simp only [hf]
    positivity
  have hmono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n hm hmn
    simp only [hf]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hlpos : 0 < Real.log ((m : ℝ) * L) := Real.log_pos (by nlinarith)
    apply inv_anti₀
    · positivity
    · gcongr
  rw [← summable_condensed_iff_of_nonneg hnn hmono]
  have hS : Summable (fun k : ℕ ↦ ((Real.log 2) ^ (1 + ε))⁻¹ * ((k : ℝ) ^ (1 + ε))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by linarith)).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hS ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlow : (k : ℝ) * Real.log 2 ≤ Real.log ((2 : ℝ) ^ k * L) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have := Real.log_pos hL1
    linarith
  have hpos : 0 < (k : ℝ) * Real.log 2 := by positivity
  have hval : (2 : ℝ) ^ k * f (2 ^ k) = ((Real.log ((2 : ℝ) ^ k * L)) ^ (1 + ε))⁻¹ := by
    simp only [hf, hcast]
    have : 0 < (Real.log ((2 : ℝ) ^ k * L)) ^ (1 + ε) := by
      apply Real.rpow_pos_of_pos; linarith
    field_simp
  have hlp : 0 ≤ Real.log ((2 : ℝ) ^ k * L) := by linarith
  rw [hval, Real.norm_of_nonneg (by positivity)]
  calc ((Real.log ((2 : ℝ) ^ k * L)) ^ (1 + ε))⁻¹ ≤ (((k : ℝ) * Real.log 2) ^ (1 + ε))⁻¹ := by
        apply inv_anti₀ (by positivity)
        gcongr
    _ = ((Real.log 2) ^ (1 + ε))⁻¹ * ((k : ℝ) ^ (1 + ε))⁻¹ := by
        rw [Real.mul_rpow (by positivity) hlog2.le, mul_inv, mul_comm]

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3.H2 :=
  OMA.bertrand
