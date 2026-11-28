import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3
import Mathlib.Analysis.PSeries

/-!
Step H2 of Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R3.
For m at least one, the bound 1/(m+1)^2 is dominated by 1/m^2, a convergent p-series,
so the condensed sequence 2^m f(2^m) is eventually dominated by a summable sequence.
Cauchy condensation for nonnegative antitone sequences then gives summability of f.
-/

namespace OMA.Helpers

theorem e142_r3_inv_sq_succ_le (m : ℕ) (hm : 1 ≤ m) :
    1 / ((m : ℝ) + 1) ^ 2 ≤ 1 / (m : ℝ) ^ 2 := by
  have hpos : (0 : ℝ) < m := by exact_mod_cast hm
  gcongr <;> linarith

end OMA.Helpers

open Filter in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3.H2 := by
  intro f hf0 hfa hev
  have hcond : Summable (fun m : ℕ => (2 : ℝ) ^ m * f (2 ^ m)) := by
    refine Summable.of_norm_bounded_eventually_nat
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)) ?_
    filter_upwards [hev, eventually_ge_atTop 1] with m hm h1
    rw [Real.norm_of_nonneg (by have := hf0 (2 ^ m); positivity)]
    exact hm.trans (OMA.Helpers.e142_r3_inv_sq_succ_le m h1)
  exact (summable_condensed_iff_of_nonneg hf0 (fun _ _ _ hle => hfa hle)).mp hcond
