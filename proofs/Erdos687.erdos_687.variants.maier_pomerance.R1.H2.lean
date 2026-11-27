import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R1
import Mathlib

/-!
# Step proof: hypothesis H2 of the Maier–Pomerance reduction for Erdős 687

For every real exponent `C` and every `ε > 0`, `x * (log x) ^ 2 * (log log x) ^ C` is
`O (x * (log x) ^ (2 + ε))`.  The point is that any power of `log log x` loses to any
positive power of `log x`: after cancelling `x * (log x) ^ 2` the quotient is
`(log log x) ^ C / (log x) ^ ε`; with `u = log x → ∞` its logarithm is `log (log u) * C - log u * ε`,
and since `log (log u) / log u → 0` this exponent tends to `-∞`.
-/

-- Step Erdos687.erdos_687.variants.maier_pomerance.R1.H2: hypothesis H2 of reduction Erdos687.erdos_687.variants.maier_pomerance.R1
-- Credit: @zhongguojwj

open Asymptotics Filter
open scoped Topology

/-- For any real exponent `C` and any `ε > 0`, `(log u) ^ C` is `O (u ^ ε)`. -/
private theorem log_pow_isBigO_rpow (C ε : ℝ) (hε : 0 < ε) :
    (fun u : ℝ ↦ Real.log u ^ C) =O[atTop] (fun u : ℝ ↦ u ^ ε) := by
  have h₁ : Tendsto (fun u : ℝ ↦ Real.log (Real.log u) / Real.log u) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have h₂ : Tendsto (fun u : ℝ ↦ C * (Real.log (Real.log u) / Real.log u)) atTop (𝓝 0) := by
    simpa using h₁.const_mul C
  have hpos : ∀ᶠ u in (atTop : Filter ℝ), 2 ≤ u := Filter.eventually_ge_atTop (2 : ℝ)
  have hsmall : ∀ᶠ u in (atTop : Filter ℝ), |C * (Real.log (Real.log u) / Real.log u)| < ε / 2 := by
    have h := h₂.eventually (Metric.ball_mem_nhds (0 : ℝ) (show 0 < ε / 2 by linarith))
    filter_upwards [h] with u hu
    rw [Real.dist_eq] at hu
    simpa using hu
  have hA : ∀ᶠ u in (atTop : Filter ℝ),
      Real.log (Real.log u) * C - Real.log u * ε ≤ (ε / 2) * -Real.log u := by
    filter_upwards [hpos, hsmall] with u hu hu'
    have hlu : 0 < Real.log u := Real.log_pos (by linarith)
    have hne : Real.log u ≠ 0 := ne_of_gt hlu
    rw [abs_lt] at hu'
    have hrc : Real.log (Real.log u) / Real.log u * C - ε < -(ε / 2) := by
      rw [mul_comm]; linarith
    calc Real.log (Real.log u) * C - Real.log u * ε
        = Real.log u * (Real.log (Real.log u) / Real.log u * C - ε) := by field_simp
      _ ≤ Real.log u * (-(ε / 2)) := mul_le_mul_of_nonneg_left hrc.le hlu.le
      _ = (ε / 2) * -Real.log u := by ring
  have hneg : Tendsto (fun u : ℝ ↦ -Real.log u) atTop atBot := by
    rw [tendsto_atBot]
    intro b
    filter_upwards [Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (-b))] with u hu
    linarith
  have hB : Tendsto (fun u : ℝ ↦ (ε / 2) * -Real.log u) atTop atBot :=
    Tendsto.const_mul_atBot (by linarith) hneg
  have hbot : Tendsto (fun u : ℝ ↦ Real.log (Real.log u) * C - Real.log u * ε) atTop atBot := by
    rw [tendsto_atBot]
    intro b
    filter_upwards [hA, (tendsto_atBot.1 hB) b] with u h1 h2
    exact le_trans h1 h2
  have hEq : (fun u : ℝ ↦ Real.log u ^ C / u ^ ε) =ᶠ[atTop]
      (fun u : ℝ ↦ Real.exp (Real.log (Real.log u) * C - Real.log u * ε)) := by
    filter_upwards [hpos] with u hu
    have hu0 : 0 < u := by linarith
    have hlu : 0 < Real.log u := Real.log_pos (by linarith)
    rw [Real.rpow_def_of_pos hlu, Real.rpow_def_of_pos hu0, Real.exp_sub]
  have hD : Tendsto (fun u : ℝ ↦ Real.log u ^ C / u ^ ε) atTop (𝓝 0) :=
    (Real.tendsto_exp_atBot.comp hbot).congr' hEq.symm
  rw [isBigO_iff_div_isBoundedUnder (by
    filter_upwards [hpos] with u hu
    have hu0 : 0 < u := by linarith
    have hpow : u ^ ε ≠ 0 := Real.rpow_pos_of_pos hu0 ε |>.ne'
    exact fun h => absurd h hpow)]
  refine ⟨1, ?_⟩
  rw [Filter.eventually_map]
  have hEq' : ∀ᶠ u in (atTop : Filter ℝ),
      Real.log u ^ C / u ^ ε = Real.exp (Real.log (Real.log u) * C - Real.log u * ε) := hEq
  have h : ∀ᶠ u in (atTop : Filter ℝ), dist (Real.log u ^ C / u ^ ε) 0 < 1 :=
    hD.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos)
  filter_upwards [hEq', h] with u hu1 hu2
  rw [Real.dist_eq, sub_zero, hu1, abs_of_pos (Real.exp_pos _)] at hu2
  rw [hu1]
  simpa using hu2.le

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R1.H2 := by
  intro C ε hε
  have key : (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) ^ C) =O[atTop]
      (fun x : ℕ ↦ Real.log (x : ℝ) ^ ε) := by
    have h1 := (log_pow_isBigO_rpow C ε hε).comp_tendsto Real.tendsto_log_atTop
    have h2 := h1.comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ ↦ (x : ℝ)) atTop atTop)
    simpa only [Function.comp_def] using h2
  have hgeo : ∀ᶠ x in (atTop : Filter ℕ), 3 ≤ x := Filter.eventually_ge_atTop (3 : ℕ)
  rw [isBigO_iff_div_isBoundedUnder (by
    filter_upwards [hgeo] with x hx
    intro h
    have hx1 : 1 < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
    have hx0 : 0 < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
    have hlp := Real.log_pos hx1
    have : 0 < (x : ℝ) * Real.log (x : ℝ) ^ (2 + ε) := by positivity
    linarith)]
  obtain ⟨c, hc⟩ := (isBigO_iff_div_isBoundedUnder (by
    filter_upwards [hgeo] with x hx
    have hx1 : 1 < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
    have hpow : Real.log (x : ℝ) ^ ε ≠ 0 :=
      Real.rpow_pos_of_pos (Real.log_pos hx1) ε |>.ne'
    exact fun h => absurd h hpow)).mp key
  refine ⟨c, ?_⟩
  rw [Filter.eventually_map] at hc ⊢
  filter_upwards [hgeo, hc] with x hx hcx
  have hx1 : 1 < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
  have hx0 : 0 < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hlp := Real.log_pos hx1
  have hne : (x : ℝ) * Real.log (x : ℝ) ^ (2 : ℝ) ≠ 0 := by positivity
  rw [Real.rpow_add hlp, ← mul_assoc, mul_div_mul_left _ _ hne]
  exact hcx
