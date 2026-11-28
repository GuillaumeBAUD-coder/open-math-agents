import OMAReductions.R_Erdos830_erdos_830_variants_pomerance_R1
import Mathlib

open Real
-- Step Erdos830.erdos_830.variants.pomerance.R1.H2: hypothesis H2 of reduction Erdos830.erdos_830.variants.pomerance.R1
-- Credit: @ivillar

/-!
# Pomerance's exponent beats the cube root of `log x`

Write `L = log x`. For large `x` we have `|o x| ≤ 1 / 4`, `log log L ≥ 1` and `L ≥ 4096`, so
`(1 / 2 + o x) * √(L * log log L) ≥ √L / 4 = L ^ (1 / 3) * L ^ (1 / 6) / 4 ≥ L ^ (1 / 3)`.
-/

namespace Erdos830CompareStep

open Filter Asymptotics

theorem compare : ∀ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) → ∀ᶠ x : ℝ in atTop,
  x * exp (-(1 / 2 + o x) * sqrt (log x * log (log (log x)))) ≤
    x * exp (-nthRoot 3 (log x)) := by
  intro o ho
  have hb := ho.bound (show (0 : ℝ) < 1 / 4 by norm_num)
  have hL : Tendsto log atTop atTop := tendsto_log_atTop
  have hL3 : Tendsto (fun x : ℝ => log (log (log x))) atTop atTop :=
    hL.comp (hL.comp hL)
  filter_upwards [hb, hL.eventually (eventually_ge_atTop 4096),
    hL3.eventually (eventually_ge_atTop 1), eventually_ge_atTop 0] with x h1 h2 h3 h4
  have habs : |o x| ≤ 1 / 4 := by simpa using h1
  have ho' : -(1 / 4 : ℝ) ≤ o x := by linarith [neg_abs_le (o x)]
  have hL0 : (0 : ℝ) < log x := by linarith
  have hroot : nthRoot 3 (log x) = log x ^ (((3 : ℕ) : ℝ)⁻¹) :=
    nthRoot_of_nonneg hL0.le
  have hsq : sqrt (log x) ≤
      sqrt (log x * log (log (log x))) :=
    sqrt_le_sqrt (by nlinarith)
  have h6 : (4 : ℝ) ≤ log x ^ (((6 : ℕ) : ℝ)⁻¹) := by
    calc (4 : ℝ) = ((4 : ℝ) ^ (6 : ℕ)) ^ (((6 : ℕ) : ℝ)⁻¹) :=
          (pow_rpow_inv_natCast (by norm_num) (by norm_num)).symm
      _ ≤ log x ^ (((6 : ℕ) : ℝ)⁻¹) :=
          rpow_le_rpow (by norm_num) (by norm_num; linarith) (by norm_num)
  have hsplit : sqrt (log x) =
      log x ^ (((3 : ℕ) : ℝ)⁻¹) * log x ^ (((6 : ℕ) : ℝ)⁻¹) := by
    rw [sqrt_eq_rpow, ← rpow_add hL0]
    congr 1
    norm_num
  have hpos : 0 ≤ log x ^ (((3 : ℕ) : ℝ)⁻¹) := rpow_nonneg hL0.le _
  have hcube : log x ^ (((3 : ℕ) : ℝ)⁻¹) ≤ 1 / 4 * sqrt (log x) := by
    rw [hsplit]
    nlinarith
  have hs0 : 0 ≤ sqrt (log x * log (log (log x))) := sqrt_nonneg _
  refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) h4
  rw [hroot]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 / 2 + o x - 1 / 4 by linarith) hs0]

end Erdos830CompareStep

theorem OMA.solution : OMA.R_Erdos830_erdos_830_variants_pomerance_R1.H2 :=
  Erdos830CompareStep.compare
