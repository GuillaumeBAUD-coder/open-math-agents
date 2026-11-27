import OMAReductions.R_Erdos936_erdos_936_variants_factorial_sub_one_R1
import Mathlib

/-! Since `primorial n ≤ 4 ^ n`, it suffices that `C * (4 ^ e) ^ n < n!` eventually, which holds
because `K ^ n / n! → 0`. -/

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_factorial_sub_one_R1.H2 := by
  intro C e
  have h := (FloorSemiring.tendsto_pow_div_factorial_atTop ((4 ^ e : ℕ) : ℝ)).const_mul (C : ℝ)
  rw [mul_zero] at h
  filter_upwards [h.eventually (gt_mem_nhds one_pos)] with n hn
  have hf : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  rw [← mul_div_assoc, div_lt_one hf] at hn
  have hlt : C * (4 ^ e) ^ n < n.factorial := by exact_mod_cast hn
  have hpr : (primorial n) ^ e ≤ (4 ^ e) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (primorial_le_four_pow n) e
  calc C * (primorial n) ^ e ≤ C * (4 ^ e) ^ n := Nat.mul_le_mul_left C hpr
    _ < n.factorial := hlt
