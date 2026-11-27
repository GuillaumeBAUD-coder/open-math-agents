import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R1

open Asymptotics Filter
open scoped Topology

-- Step Erdos687.erdos_687.variants.maier_pomerance.R1.H2
-- Credit: @NSXSHINOBI

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R1.H2 := by
  intro C ε hε
  have hlogtop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall :
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) ^ C) =o[atTop]
        (fun x : ℕ ↦ Real.log (x : ℝ) ^ ε) :=
    (isLittleO_log_rpow_rpow_atTop C hε).comp_tendsto hlogtop
  have hmul :
      (fun x : ℕ ↦ ((x : ℝ) * Real.log x ^ (2 : ℝ)) * Real.log (Real.log x) ^ C) =o[atTop]
        (fun x : ℕ ↦ ((x : ℝ) * Real.log x ^ (2 : ℝ)) * Real.log x ^ ε) :=
    (isBigO_refl _ _).mul_isLittleO hsmall
  refine hmul.isBigO.congr' ?_ ?_
  · filter_upwards with x
    ring
  · filter_upwards [eventually_gt_atTop 1] with x hx
    have hxpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
    rw [Real.rpow_add hxpos]
    ring
