import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R1

open Asymptotics Filter Real

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R1.H2 := by
  intro C ε hε
  have ht : Tendsto (fun x : ℕ ↦ log (x : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := ((isLittleO_log_rpow_rpow_atTop C hε).isBigO.comp_tendsto ht)
  have hmul := (isBigO_refl (fun x : ℕ ↦ (x : ℝ) * log x ^ (2 : ℝ)) atTop).mul h
  refine hmul.congr' (Eventually.of_forall fun _ ↦ rfl) ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with x hx
  change (x : ℝ) * log x ^ (2 : ℝ) * log x ^ ε = _
  rw [mul_assoc, ← Real.rpow_add (Real.log_pos (by exact_mod_cast hx))]
