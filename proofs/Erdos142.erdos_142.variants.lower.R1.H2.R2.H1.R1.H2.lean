import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R2.H1.R1.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R1.H2.R2.H1.R1
-- Credit: @LAPRAI

open Real Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1.H2 := by
  intro C c η hC hc hη
  have hL : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hp : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp hl
  filter_upwards [hL.eventually_ge_atTop 2, hl.eventually_gt_atTop (Real.log (16 * C)),
    hl.eventually_gt_atTop 0, hp.eventually_ge_atTop (5 / c)] with N h2 hlb hl0 hpw
  set L := Real.log (N : ℝ) with hLdef
  set l := Real.log L with hldef
  have hLpos : 0 < L := by linarith
  have hcast : (((⌈L⌉₊ + 1) ^ 4 : ℕ) : ℝ) = ((⌈L⌉₊ : ℝ) + 1) ^ 4 := by push_cast; ring
  have hX : ((⌈L⌉₊ : ℝ) + 1) ^ 4 ≤ 16 * Real.exp (4 * l) := by
    have hc1 : (⌈L⌉₊ : ℝ) + 1 ≤ 2 * L := by
      have := Nat.ceil_lt_add_one hLpos.le; linarith
    have hE : Real.exp (4 * l) = L ^ 4 := by
      rw [show (4 : ℝ) * l = ((4 : ℕ) : ℝ) * l by norm_num, Real.exp_nat_mul, hldef,
        Real.exp_log hLpos]
    rw [hE]
    calc ((⌈L⌉₊ : ℝ) + 1) ^ 4 ≤ (2 * L) ^ 4 := by gcongr
      _ = 16 * L ^ 4 := by ring
  have hsplit : l ^ (1 + η) = l * l ^ η := by
    rw [Real.rpow_add hl0, Real.rpow_one]
  have hkey : 5 * l ≤ c * l ^ (1 + η) := by
    rw [hsplit]
    have h5 : 5 ≤ c * l ^ η := by rw [div_le_iff₀ hc] at hpw; linarith
    nlinarith
  have h16 : 16 * C < Real.exp l := by
    have := Real.exp_lt_exp.mpr hlb
    rwa [Real.exp_log (by positivity)] at this
  rw [hcast]
  calc C * ((⌈L⌉₊ : ℝ) + 1) ^ 4 * Real.exp (-c * l ^ (1 + η))
      ≤ C * (16 * Real.exp (4 * l)) * Real.exp (-c * l ^ (1 + η)) := by gcongr
    _ = 16 * C * Real.exp (4 * l + -c * l ^ (1 + η)) := by rw [Real.exp_add]; ring
    _ ≤ 16 * C * Real.exp (-l) := by
      gcongr; linarith [neg_mul c (l ^ (1 + η))]
    _ < 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]; exact h16
