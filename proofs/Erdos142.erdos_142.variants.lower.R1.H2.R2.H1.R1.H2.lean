import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1
import Mathlib

/-! With x = log log N, (ceil (log N) + 1)^4 is at most 16 e^(4x), and x (c x^eta - 4) tends to infinity,
so C (ceil (log N) + 1)^4 exp(-c x^(1+eta)) is eventually below 1. -/

open Filter Real Topology

namespace OMA.E142Poly

theorem key (C c η : ℝ) (hC : 0 < C) (hc : 0 < c) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, C * (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) *
      Real.exp (-c * (Real.log (Real.log (N : ℝ))) ^ (1 + η)) < 1 := by
  have hx : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hg : Tendsto (fun x : ℝ => x * (c * x ^ η + (-4))) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ (tendsto_atTop_add_const_right _ (-4) ((tendsto_rpow_atTop hη).const_mul_atTop hc))
  have hE : Tendsto (fun x : ℝ => Real.exp (-(x * (c * x ^ η + (-4))))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hg
  have hev := (hE.comp hx).eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / (16 * C) by positivity))
  filter_upwards [hev, eventually_ge_atTop 8, hx.eventually (eventually_gt_atTop 0)] with N hN hN8 hxpos
  simp only [Function.comp] at hN
  set L := Real.log (N : ℝ) with hLdef
  set x := Real.log L with hxdef
  have he2 : Real.exp 2 < 8 := by
    have h1 := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  have hL2 : 2 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    exact he2.le.trans (by exact_mod_cast hN8)
  have hLpos : 0 < L := by linarith
  have hceil : ((⌈L⌉₊ : ℝ) + 1) ≤ 2 * L := by
    have := Nat.ceil_lt_add_one hLpos.le; linarith
  have hcast : (((⌈L⌉₊ + 1) ^ 4 : ℕ) : ℝ) = ((⌈L⌉₊ : ℝ) + 1) ^ 4 := by push_cast; ring
  have hpow4 : ((⌈L⌉₊ : ℝ) + 1) ^ 4 ≤ 16 * Real.exp (4 * x) := by
    have hLx : L = Real.exp x := (Real.exp_log hLpos).symm
    calc ((⌈L⌉₊ : ℝ) + 1) ^ 4 ≤ (2 * L) ^ 4 := pow_le_pow_left₀ (by positivity) hceil 4
      _ = 16 * L ^ 4 := by ring
      _ = 16 * Real.exp (4 * x) := by rw [hLx, ← Real.exp_nat_mul]; norm_num
  have hsplit : x ^ (1 + η) = x * x ^ η := by
    rw [Real.rpow_add hxpos, Real.rpow_one]
  have hexp : Real.exp (4 * x) * Real.exp (-c * x ^ (1 + η)) = Real.exp (-(x * (c * x ^ η + (-4)))) := by
    rw [← Real.exp_add, hsplit]; congr 1; ring
  rw [hcast]
  calc C * ((⌈L⌉₊ : ℝ) + 1) ^ 4 * Real.exp (-c * x ^ (1 + η))
      ≤ C * (16 * Real.exp (4 * x)) * Real.exp (-c * x ^ (1 + η)) := by
        gcongr
    _ = 16 * C * Real.exp (-(x * (c * x ^ η + (-4)))) := by rw [← hexp]; ring
    _ < 16 * C * (1 / (16 * C)) := by gcongr
    _ = 1 := by field_simp

end OMA.E142Poly

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1.H2 :=
  fun C c η hC hc hη => OMA.E142Poly.key C c η hC hc hη
