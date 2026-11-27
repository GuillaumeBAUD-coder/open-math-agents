import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R1

-- Step Erdos687.erdos_687.variants.maier_pomerance.R1.H2: hypothesis H2 of reduction
-- Erdos687.erdos_687.variants.maier_pomerance.R1
-- Credit: @OrangeHeadz
-- H2 := ∀ C ε : ℝ, 0 < ε →
--   (fun x : ℕ ↦ (x : ℝ) * Real.log x ^ (2 : ℝ) * Real.log (Real.log x) ^ C)
--     =O[atTop] (fun x : ℕ ↦ (x : ℝ) * Real.log x ^ (2 + ε))

/-! # Any fixed power of `log log x` is absorbed by an extra power of `log x`

`(log y) ^ C = o(y ^ ε)` as `y → ∞`, for every real `C` and every `ε > 0`. Substituting
`y = log x` gives `(log log x) ^ C = O((log x) ^ ε)` along the naturals. Multiplying by
`x * (log x) ^ 2` and using `(log x) ^ 2 * (log x) ^ ε = (log x) ^ (2 + ε)` once `log x > 0`
gives the claim. -/

open Asymptotics Filter

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R1.H2 := by
  intro C ε hε
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : (fun x : ℕ => Real.log (Real.log (x : ℝ)) ^ C) =O[atTop]
      (fun x : ℕ => Real.log (x : ℝ) ^ ε) :=
    ((isLittleO_log_rpow_rpow_atTop C hε).comp_tendsto hlog).isBigO
  have h2 : (fun x : ℕ => (x : ℝ) * Real.log (x : ℝ) ^ (2 : ℝ)) =O[atTop]
      (fun x : ℕ => (x : ℝ) * Real.log (x : ℝ) ^ (2 : ℝ)) := isBigO_refl _ _
  refine (h2.mul h1).congr' (Eventually.of_forall fun _ => rfl) ?_
  filter_upwards [hlog.eventually_gt_atTop 0] with x hx
  show (x : ℝ) * Real.log x ^ (2 : ℝ) * Real.log x ^ ε = (x : ℝ) * Real.log x ^ (2 + ε)
  rw [mul_assoc, ← Real.rpow_add hx]
