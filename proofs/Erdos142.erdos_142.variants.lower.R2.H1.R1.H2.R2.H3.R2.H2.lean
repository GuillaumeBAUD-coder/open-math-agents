import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2
import Mathlib

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2.H2 := by
  intro C c e hC hc he
  apply Summable.mul_left
  have hs : Summable (fun j : ℕ => ((j : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat hs ?_
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hL : 0 < Real.log 4 ^ e := Real.rpow_pos_of_pos hl4 _
  obtain ⟨K, hK⟩ : ∃ K, K = 4 / (e * c * Real.log 4 ^ e) := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; positivity
  have hcLK : c * Real.log 4 ^ e * K = 4 / e := by
    rw [hK]
    field_simp
  obtain ⟨M, hM⟩ := exists_nat_gt (K ^ (2 / e))
  filter_upwards [Filter.eventually_ge_atTop M, Filter.eventually_ge_atTop 1] with j hj hj1
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  have hKj : K ^ (2 / e) ≤ j := hM.le.trans (by exact_mod_cast hj)
  obtain ⟨y, hy⟩ : ∃ y, y = (j : ℝ) ^ (e / 2) := ⟨_, rfl⟩
  have hypos : 0 < y := by rw [hy]; exact Real.rpow_pos_of_pos hjpos _
  have h1 : K ≤ y := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hKpos.le _) hKj (by positivity : (0 : ℝ) ≤ e / 2)
    rw [← Real.rpow_mul hKpos.le, show 2 / e * (e / 2) = 1 by field_simp, Real.rpow_one] at this
    rw [hy]
    exact this
  have h2 : Real.log j ≤ y / (e / 2) := by
    rw [hy]
    exact Real.log_le_rpow_div hjpos.le (by positivity)
  have h2' : 2 * Real.log j ≤ 4 / e * y := by
    have : y / (e / 2) = 2 / e * y := by field_simp
    rw [this] at h2
    have h4 : 4 / e * y = 2 * (2 / e * y) := by ring
    rw [h4]
    linarith
  have h3 : ((j : ℝ) * Real.log 4) ^ e = y * y * Real.log 4 ^ e := by
    rw [Real.mul_rpow hjpos.le hl4.le, hy, ← Real.rpow_add hjpos]
    congr 2
    ring
  have h5 : 4 / e * y ≤ c * (y * y * Real.log 4 ^ e) := by
    have h6 : c * Real.log 4 ^ e * K ≤ c * Real.log 4 ^ e * y :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [hcLK] at h6
    have h7 := mul_le_mul_of_nonneg_right h6 hypos.le
    linarith
  calc Real.exp (-c * ((j : ℝ) * Real.log 4) ^ e) ≤ Real.exp (-(2 * Real.log j)) := by
        apply Real.exp_le_exp.mpr
        rw [h3]
        linarith
    _ = ((j : ℝ) ^ 2)⁻¹ := by
        rw [Real.exp_neg, show 2 * Real.log (j : ℝ) = Real.log j + Real.log j by ring,
          Real.exp_add, Real.exp_log hjpos, sq]
