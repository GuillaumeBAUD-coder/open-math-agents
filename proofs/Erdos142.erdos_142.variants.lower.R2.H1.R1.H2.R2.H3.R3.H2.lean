import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Cauchy condensation: the condensed terms are (k log 2 + log log 4)^(-(1+eps)),
-- bounded by a constant times (k+1)^(-(1+eps)), a convergent p-series.

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3.H2 := by
  unfold OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3.H2
  intro ε hε
  set c := Real.log 4 with hc
  have h4 : (4:ℝ) = 2 ^ 2 := by norm_num
  have hc' : c = 2 * Real.log 2 := by rw [hc, h4, Real.log_pow]; push_cast; ring
  have hc1 : 1 < c := by rw [hc']; have := Real.log_two_gt_d9; linarith
  have hc2 : c ≤ 2 := by rw [hc']; have := Real.log_two_lt_d9; linarith
  have hlc : 0 < Real.log c := Real.log_pos hc1
  have hlc2 : Real.log c ≤ Real.log 2 := Real.log_le_log (by linarith) hc2
  set p := 1 + ε with hp
  have hp1 : 1 < p := by linarith
  have hp0 : 0 ≤ p := by linarith
  set f : ℕ → ℝ := fun j ↦ ((j : ℝ) * (Real.log ((j : ℝ) * c)) ^ p)⁻¹ with hf
  have hlogpos : ∀ m : ℕ, 0 < m → 0 < Real.log ((m:ℝ) * c) := by
    intro m hm
    apply Real.log_pos
    have : (1:ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have h_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [hf, h]
    · have := hlogpos n h
      positivity
  have h_mono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n hm hmn
    have hm' := hlogpos m hm
    have hmr : (0:ℝ) < m := by exact_mod_cast hm
    have hmn' : (m:ℝ) ≤ n := by exact_mod_cast hmn
    simp only [hf]
    apply inv_anti₀ (by positivity)
    apply mul_le_mul hmn' _ (by positivity) (by linarith)
    apply Real.rpow_le_rpow hm'.le _ hp0
    apply Real.log_le_log (by positivity)
    nlinarith
  rw [← summable_condensed_iff_of_nonneg h_nonneg h_mono]
  have hg : Summable (fun k : ℕ ↦ ((Real.log c) ^ p)⁻¹ * (((k:ℝ) + 1) ^ p)⁻¹) := by
    apply Summable.mul_left
    have := (Real.summable_nat_rpow_inv (p := p)).mpr hp1
    have := (summable_nat_add_iff 1).mpr this
    simpa using this
  refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_) hg
  · exact mul_nonneg (by positivity) (h_nonneg _)
  · simp only [hf]
    push_cast
    have h2k : (0:ℝ) < 2 ^ k := by positivity
    have hL : Real.log (2 ^ k * c) = k * Real.log 2 + Real.log c := by
      rw [Real.log_mul h2k.ne' (by linarith), Real.log_pow]
    rw [hL, mul_inv, ← mul_assoc, mul_inv_cancel₀ h2k.ne', one_mul, ← mul_inv,
      ← Real.mul_rpow hlc.le (by positivity)]
    apply inv_anti₀ (by positivity)
    apply Real.rpow_le_rpow (by positivity) _ hp0
    have : (0:ℝ) ≤ k := by positivity
    nlinarith
