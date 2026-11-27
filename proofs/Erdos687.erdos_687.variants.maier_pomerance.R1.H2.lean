import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R1
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Asymptotics Filter
open scoped Topology

namespace OMA.SE687

lemma loglog_rpow_isLittleO_rpow (C eps : ℝ) (heps : 0 < eps) :
    (fun x : ℕ => Real.log (Real.log x) ^ C) =o[atTop] (fun x : ℕ => Real.log x ^ eps) := by
  have h1 : (fun t : ℝ => Real.log t ^ C) =o[atTop] (fun t : ℝ => t ^ eps) :=
    isLittleO_log_rpow_rpow_atTop C heps
  have h2 : (fun t : ℝ => Real.log (Real.log t) ^ C) =o[atTop]
      (fun t : ℝ => Real.log t ^ eps) := h1.comp_tendsto Real.tendsto_log_atTop
  have h3 := h2.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def] using h3

end OMA.SE687

theorem OMA.solution :
    OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R1.H2 := by
  intro C eps heps
  have hkey := OMA.SE687.loglog_rpow_isLittleO_rpow C eps heps
  have hmul : (fun x : ℕ => Real.log (Real.log x) ^ C * ((x : ℝ) * Real.log x ^ (2 : ℝ)))
      =o[atTop] (fun x : ℕ => Real.log x ^ eps * ((x : ℝ) * Real.log x ^ (2 : ℝ))) :=
    hkey.mul_isBigO (isBigO_refl _ _)
  refine hmul.isBigO.congr' ?_ ?_
  · filter_upwards with x
    ring
  · filter_upwards [eventually_ge_atTop 3] with x hx
    have hlog : 0 < Real.log x := Real.log_pos (by exact_mod_cast (show (1 : ℕ) < x by omega))
    rw [mul_comm (Real.log x ^ eps), mul_assoc, ← Real.rpow_add hlog]
