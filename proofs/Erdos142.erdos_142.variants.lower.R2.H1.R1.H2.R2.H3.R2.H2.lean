import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2
import Mathlib

/-!
Step H2 of reduction R2.H1.R1.H2.R2.H3.R2 of Erdős 142 (reduction by @eolo12): for positive
C, c, e the series of C * exp (-c * (j * log 4) ^ e) over the natural numbers j converges.

Proof: log 4 ≥ 1, so (j log 4)^e ≥ j^e = j^(e/2) * j^(e/2). Since log j ≤ j^(e/2) / (e/2) and
j^(e/2) ≥ 4 / (e c) for large j, we get 2 log j ≤ c (j log 4)^e, so the j-th term is at most
C * j^(-2) from some point on.
-/

namespace OMASumm142

theorem summ (C c e : ℝ) (hc : 0 < c) (he : 0 < e) :
    Summable (fun j : ℕ ↦ C * Real.exp (-c * ((j : ℝ) * Real.log 4) ^ e)) := by
  apply Summable.mul_left
  have hs : Summable (fun j : ℕ => (j : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have h : Real.exp 1 ≤ 4 := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 4 := Real.log_le_log (Real.exp_pos 1) h
  have hev : ∀ᶠ j : ℕ in Filter.atTop, 4 / (e * c) ≤ (j : ℝ) ^ (e / 2) := by
    have h1 : Filter.Tendsto (fun j : ℕ => (j : ℝ) ^ (e / 2)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (by positivity : 0 < e / 2)).comp tendsto_natCast_atTop_atTop
    exact h1.eventually_ge_atTop _
  apply Summable.of_norm_bounded_eventually_nat hs
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with j hj hj1
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.rpow_def_of_pos hjpos]
  apply Real.exp_le_exp.mpr
  have h1 : Real.log j ≤ (j : ℝ) ^ (e / 2) / (e / 2) :=
    Real.log_le_rpow_div hjpos.le (by positivity)
  have h2 : (j : ℝ) ^ e ≤ ((j : ℝ) * Real.log 4) ^ e :=
    Real.rpow_le_rpow hjpos.le (by nlinarith) he.le
  have h3 : (j : ℝ) ^ e = (j : ℝ) ^ (e / 2) * (j : ℝ) ^ (e / 2) := by
    rw [← Real.rpow_add hjpos]
    ring_nf
  have hpow : 0 < (j : ℝ) ^ (e / 2) := Real.rpow_pos_of_pos hjpos _
  have h5 : 4 / e ≤ c * (j : ℝ) ^ (e / 2) := by
    have h := mul_le_mul_of_nonneg_left hj hc.le
    calc 4 / e = c * (4 / (e * c)) := by field_simp
      _ ≤ _ := h
  have h6 : 2 * Real.log j ≤ 4 / e * (j : ℝ) ^ (e / 2) := by
    have h : (j : ℝ) ^ (e / 2) / (e / 2) = 2 / e * (j : ℝ) ^ (e / 2) := by field_simp
    rw [h] at h1
    have h' : 4 / e * (j : ℝ) ^ (e / 2) = 2 * (2 / e * (j : ℝ) ^ (e / 2)) := by ring
    linarith
  have h7 : 4 / e * (j : ℝ) ^ (e / 2) ≤ c * (j : ℝ) ^ e := by
    rw [h3]
    nlinarith
  have h8 := mul_le_mul_of_nonneg_left h2 hc.le
  linarith

end OMASumm142

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2.H2 := by
  intro C c e _ hc he
  exact OMASumm142.summ C c e hc he
