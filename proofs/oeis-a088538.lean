import OMAStatements.S_oeis_a088538
import Mathlib

namespace OMA.A088538Proof

open OMA.S_oeis_a088538 Filter Topology Real

noncomputable def th (n : ℕ) : ℝ := π / 2 ^ (n + 2)

theorem th_pos (n : ℕ) : 0 < th n := by unfold th; positivity

theorem th_lt (n : ℕ) : th n < π / 2 := by
  unfold th
  have h4 : (4 : ℝ) ≤ 2 ^ (n + 2) := by
    rw [pow_add]; norm_num
    exact one_le_pow₀ (by norm_num)
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [pi_pos]

theorem th_succ (n : ℕ) : th n = 2 * th (n + 1) := by
  unfold th; field_simp; ring

theorem sin_th_pos (n : ℕ) : 0 < sin (th n) :=
  sin_pos_of_pos_of_lt_pi (th_pos n) (by linarith [th_lt n, pi_pos])

theorem cos_th_pos (n : ℕ) : 0 < cos (th n) :=
  cos_pos_of_mem_Ioo ⟨by linarith [th_pos n, pi_pos], th_lt n⟩

theorem half_re (z : ℂ) (r : ℝ) : ((z + r) / 2).re = (z.re + r) / 2 := by simp

theorem half_im (z : ℂ) (r : ℝ) : ((z + r) / 2).im = z.im / 2 := by simp

theorem u_eq (n : ℕ) :
    u n = ⟨cos (th n) / (2 ^ n * sin (th n)), 1 / 2 ^ n⟩ := by
  induction n with
  | zero =>
    have : th 0 = π / 4 := by unfold th; norm_num
    rw [this, cos_pi_div_four, sin_pi_div_four]
    apply Complex.ext
    · simp [u]
    · simp [u]
  | succ n ih =>
    have hs := sin_th_pos n
    have hk : (0 : ℝ) < 2 ^ n := by positivity
    have hnorm : ‖u n‖ = 1 / (2 ^ n * sin (th n)) := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, ih]
      dsimp only
      have e : (cos (th n) / (2 ^ n * sin (th n))) ^ 2 + (1 / 2 ^ n) ^ 2 =
          (1 / (2 ^ n * sin (th n))) ^ 2 * (sin (th n) ^ 2 + cos (th n) ^ 2) := by
        field_simp; ring
      rw [e, sin_sq_add_cos_sq, mul_one, Real.sqrt_sq (by positivity)]
    have hs' := sin_th_pos (n + 1)
    have hc' := cos_th_pos (n + 1)
    show (u n + (‖u n‖ : ℂ)) / 2 = _
    apply Complex.ext
    · rw [half_re, hnorm, ih]
      dsimp only
      rw [th_succ n, cos_two_mul, sin_two_mul, pow_succ]
      field_simp
      ring
    · rw [half_im, ih]
      dsimp only
      rw [pow_succ]
      field_simp

end OMA.A088538Proof

open OMA.A088538Proof Filter Topology Real in
theorem OMA.solution : type_of% @OMA.S_oeis_a088538.main := by
  have hre : ∀ n, (OMA.S_oeis_a088538.u n).re = 4 / π * (cos (th n) / sinc (th n)) := by
    intro n
    rw [u_eq, sinc_of_ne_zero (th_pos n).ne']
    simp only
    have hs := sin_th_pos n
    have hc := cos_th_pos n
    unfold th at *
    rw [pow_add]
    field_simp
    ring
  simp_rw [hre]
  have hth : Tendsto th atTop (𝓝 0) := by
    unfold th
    have : Tendsto (fun n : ℕ => π * ((1 / 2) ^ (n + 2) : ℝ)) atTop (𝓝 (π * 0)) := by
      apply Tendsto.const_mul
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 2)
    rw [mul_zero] at this
    refine this.congr (fun n => ?_)
    rw [one_div, inv_pow, div_eq_mul_inv]
  have h1 : Tendsto (fun n => cos (th n) / sinc (th n)) atTop (𝓝 (cos 0 / sinc 0)) :=
    ((continuous_cos.tendsto 0).comp hth).div ((continuous_sinc.tendsto 0).comp hth)
      (by rw [sinc_zero]; norm_num)
  rw [cos_zero, sinc_zero, div_one] at h1
  simpa using h1.const_mul (4 / π)
