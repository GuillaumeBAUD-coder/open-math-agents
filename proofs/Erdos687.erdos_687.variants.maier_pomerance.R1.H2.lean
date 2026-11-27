import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R1

-- Step Erdos687.erdos_687.variants.maier_pomerance.R1.H2: hypothesis H2 of reduction Erdos687.erdos_687.variants.maier_pomerance.R1
-- Credit: @ivillar
-- H2 := ∀ C ε : ℝ, 0 < ε →     (fun x : ℕ ↦ (x : ℝ) * Real.log x ^ (2 : ℝ) * Real.log (Real.log x) ^ C)       =O[atTop] (fun x : ℕ ↦ (x : ℝ) * Real.log x ^ (2 + ε))
--
-- Proof: (log y)^C = o(y^ε) as y → ∞; compose with y = log x → ∞, multiply both sides
-- by x (log x)^2, and merge the powers of log x (log x > 0 for x ≥ 2).

open Asymptotics Filter

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R1.H2 := by
  intro C ε hε
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : (fun x : ℕ => Real.log (Real.log (x : ℝ)) ^ C) =O[atTop]
      (fun x : ℕ => Real.log (x : ℝ) ^ ε) :=
    ((isLittleO_log_rpow_rpow_atTop C hε).comp_tendsto hlog).isBigO
  have h2 := (isBigO_refl (fun x : ℕ => (x : ℝ) * Real.log (x : ℝ) ^ (2 : ℝ)) atTop).mul h1
  refine h2.congr' (Eventually.of_forall fun x => rfl) ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  show (x : ℝ) * Real.log (x : ℝ) ^ (2 : ℝ) * Real.log (x : ℝ) ^ ε =
    (x : ℝ) * Real.log (x : ℝ) ^ (2 + ε)
  rw [Real.rpow_add hpos, mul_assoc]
