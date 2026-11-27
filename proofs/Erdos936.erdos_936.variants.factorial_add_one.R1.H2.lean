import OMAReductions.R_Erdos936_erdos_936_variants_factorial_add_one_R1
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecificLimits.Basic

-- Step Erdos936.erdos_936.variants.factorial_add_one.R1.H2: hypothesis H2 of reduction Erdos936.erdos_936.variants.factorial_add_one.R1
-- Credit: @jacobmath31415
-- Proof: primorial n is at most 4^n, and (4^e)^n / n! tends to 0.

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_factorial_add_one_R1.H2 := by
  intro C e
  have hT : Filter.Tendsto (fun n : ℕ => ((4 : ℝ) ^ e) ^ n / (n.factorial : ℝ))
      Filter.atTop (nhds 0) :=
    FloorSemiring.tendsto_pow_div_factorial_atTop _
  have hpos : (0 : ℝ) < 1 / ((C : ℝ) + 1) := by positivity
  filter_upwards [hT.eventually (gt_mem_nhds hpos)] with n hn
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hC : (0 : ℝ) < (C : ℝ) + 1 := by positivity
  rw [div_lt_div_iff₀ hf hC, one_mul] at hn
  have hprim : ((primorial n : ℕ) : ℝ) ^ e ≤ ((4 : ℝ) ^ e) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    gcongr
    exact_mod_cast primorial_le_four_pow n
  have h0 : (0 : ℝ) ≤ ((primorial n : ℕ) : ℝ) ^ e := by positivity
  have hreal : (C : ℝ) * ((primorial n : ℕ) : ℝ) ^ e < (n.factorial : ℝ) := by
    calc (C : ℝ) * ((primorial n : ℕ) : ℝ) ^ e
        ≤ ((C : ℝ) + 1) * ((4 : ℝ) ^ e) ^ n := by
          apply mul_le_mul (by linarith) hprim h0 (by positivity)
      _ = ((4 : ℝ) ^ e) ^ n * ((C : ℝ) + 1) := by ring
      _ < (n.factorial : ℝ) := hn
  exact_mod_cast hreal
