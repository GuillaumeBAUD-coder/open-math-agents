import OMAReductions.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1
import Mathlib

/-! # Enough primes at Konyagin's balancing scale
Apply Chebyshev's lower bound directly to a real argument, so its natural floor
is the desired cutoff. Logarithms and the additive error are absorbed separately. -/

namespace OMA.PrimeCount1109

open Filter Real

lemma prime_lower (s : ℝ) (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, x^(1-s) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := (isLittleO_log_rpow_atTop (show 0 < (1:ℝ) by norm_num)).bound
    (show 0 < Real.log 2 / 8 by positivity)
  have h2 := (isLittleO_log_rpow_atTop hs).bound (show 0 < Real.log 2 / 4 by positivity)
  filter_upwards [eventually_ge_atTop (4:ℝ),h1,h2] with x hx ha hb
  have hx0 : 0 < x := by linarith
  have hlx := Real.log_pos (show 1 < x by linarith)
  simp only [Real.norm_eq_abs, abs_of_pos hlx, Real.rpow_one, abs_of_pos hx0,
    abs_of_pos (Real.rpow_pos_of_pos hx0 s)] at ha hb
  have hau : Real.log (x+2) ≤ 2 * Real.log x := by
    calc
      _ ≤ Real.log (x^2) := Real.log_le_log (by positivity) (by nlinarith [sq_nonneg (x-2)])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hsmall : x^(1-s)*Real.log x ≤ x*(Real.log 2/4) := by
    calc
      _ ≤ x^(1-s)*(Real.log 2/4*x^s) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (Real.log 2/4)*(x^(1-s)*x^s) := by ring
      _ = _ := by rw [← Real.rpow_add hx0, sub_add_cancel, Real.rpow_one, mul_comm]
  have hnum : x*(Real.log 2/4) ≤ (x-1)*Real.log 2 - Real.log (x+2) := by
    nlinarith [mul_nonneg (show 0 ≤ x-4 by linarith) hlog.le]
  exact ((le_div_iff₀ hlx).mpr (hsmall.trans hnum)).trans (Chebyshev.pi_ge' (by linarith))

end OMA.PrimeCount1109

theorem OMA.solution : OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1.H2 := by
  intro η hη
  let c := (4:ℝ)/15
  have hc : 0 < c := by dsimp [c]; norm_num
  have hg : Filter.Tendsto (fun N : ℕ => (N:ℝ)^c) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  filter_upwards [hg.eventually (OMA.PrimeCount1109.prime_lower (η/c) (by positivity)),
    Filter.eventually_ge_atTop (1:ℕ)] with N h hn
  rw [← Nat.primesLE_eq_filter_range, Nat.primesLE_card_eq_primeCounting]
  change (N:ℝ)^(c-η) ≤ (Nat.primeCounting ⌊(N:ℝ)^c⌋₊ : ℝ)
  rw [← Real.rpow_mul (Nat.cast_nonneg N)] at h
  have he : c*(1-η/c) = c-η := by field_simp
  rwa [he] at h
