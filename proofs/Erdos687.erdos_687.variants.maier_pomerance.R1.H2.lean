import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R1
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Asymptotics Filter
open scoped Topology

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R1.H2 := by
  intro C ε hε
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hg : (fun n : ℕ => Real.log (Real.log (n : ℝ)) ^ C) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) ^ ε) :=
    ((isLittleO_log_rpow_rpow_atTop C hε).comp_tendsto hlog).isBigO
  have hm := (isBigO_refl (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ) ^ (2 : ℝ)) atTop).mul hg
  refine hm.congr' (Filter.Eventually.of_forall fun _ => rfl) ?_
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  dsimp
  rw [Real.rpow_add hn]
  ring
