import OMAReductions.R_Erdos977_erdos_977_variants_factorial_R1
import Mathlib

/-- Step Erdos977.erdos_977.variants.factorial.R1.H2. -/
theorem OMA.solution : OMA.R_Erdos977_erdos_977_variants_factorial_R1.H2 := by
  intro C K
  have h := (FloorSemiring.tendsto_pow_div_factorial_atTop (K : ℝ)).const_mul (C : ℝ)
  rw [mul_zero] at h
  filter_upwards [h.eventually (gt_mem_nhds one_pos)] with n hn
  have hf : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  rw [← mul_div_assoc, div_lt_one hf] at hn
  exact_mod_cast hn
