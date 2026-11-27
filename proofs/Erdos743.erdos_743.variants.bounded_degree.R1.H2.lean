import OMAReductions.R_Erdos743_erdos_743_variants_bounded_degree_R1
import Mathlib

/-!
Step H2 of Erdos743.erdos_743.variants.bounded_degree.R1: since log n = o(n),
eventually (d + 1) log n ≤ c n, hence d ≤ c n / log n.
-/

open Filter in
theorem OMA.solution : OMA.R_Erdos743_erdos_743_variants_bounded_degree_R1.H2 := by
  unfold OMA.R_Erdos743_erdos_743_variants_bounded_degree_R1.H2
  intro c hc d
  have hd : (0 : ℝ) < d + 1 := by positivity
  have h := (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop).bound
    (show 0 < c / ((d : ℝ) + 1) by positivity)
  filter_upwards [h, eventually_ge_atTop 2] with n hn h2
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hn' : Real.log (n : ℝ) ≤ c / ((d : ℝ) + 1) * n := by
    simp only [Function.comp_apply, id, Real.norm_eq_abs] at hn
    rwa [abs_of_pos hL, abs_of_nonneg (Nat.cast_nonneg _)] at hn
  have h3 : ((d : ℝ) + 1) * Real.log n ≤ c * n := by
    calc ((d : ℝ) + 1) * Real.log n ≤ ((d : ℝ) + 1) * (c / ((d : ℝ) + 1) * n) :=
          mul_le_mul_of_nonneg_left hn' hd.le
      _ = c * n := by field_simp
  rw [le_div_iff₀ hL]
  calc (d : ℝ) * Real.log n ≤ ((d : ℝ) + 1) * Real.log n :=
        mul_le_mul_of_nonneg_right (by linarith) hL.le
    _ ≤ c * n := h3
