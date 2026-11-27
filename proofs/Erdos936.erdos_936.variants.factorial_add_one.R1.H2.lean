import OMAReductions.R_Erdos936_erdos_936_variants_factorial_add_one_R1
import Mathlib

-- Step Erdos936.erdos_936.variants.factorial_add_one.R1.H2: hypothesis H2 of reduction Erdos936.erdos_936.variants.factorial_add_one.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! primorial n ≤ 4^n, so C (primorial n)^e ≤ C (4^e)^n, and (4^e)^n / n! → 0. -/

open Finset Filter Nat

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_factorial_add_one_R1.H2 := by
  intro C e
  have ht := FloorSemiring.tendsto_pow_div_factorial_atTop ((4 : ℝ) ^ e)
  have hpos : (0 : ℝ) < 1 / ((C : ℝ) + 1) := by positivity
  filter_upwards [ht.eventually (gt_mem_nhds hpos)] with n hn
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [div_lt_div_iff₀ hf (by positivity), one_mul] at hn
  have h1 : (C : ℝ) * ((4 : ℝ) ^ e) ^ n < n.factorial := by nlinarith
  have h2 : C * (primorial n) ^ e ≤ C * ((4 ^ e) ^ n) := by
    apply Nat.mul_le_mul_left
    calc primorial n ^ e ≤ (4 ^ n) ^ e := Nat.pow_le_pow_left (primorial_le_four_pow n) e
      _ = (4 ^ e) ^ n := by rw [← pow_mul, ← pow_mul, mul_comm]
  have h3 : ((C * ((4 ^ e) ^ n) : ℕ) : ℝ) < n.factorial := by push_cast; exact h1
  have h4 : C * ((4 ^ e) ^ n) < n.factorial := by exact_mod_cast h3
  exact lt_of_le_of_lt h2 h4
