import OMAReductions.R_Erdos4_erdos_4_variants_rankin_R1
import Mathlib

-- Step Erdos4.erdos_4.variants.rankin.R1.H2: hypothesis H2 of reduction Erdos4.erdos_4.variants.rankin.R1
-- Credit: @ivillar
-- H2 := ∃ N : ℕ, ∀ x : ℕ, N ≤ x → x ≤ Nat.primeCounting x ^ 2
--
-- Proof: Mathlib's Chebyshev bound `Chebyshev.pi_ge` gives
-- (n log 2 - log (n + 1)) / log n ≤ π n. Since √x log x = o(x), eventually
-- 2 √n log n ≤ n log 2, and log (n + 1) ≤ 2 log n ≤ √n log n once n ≥ 4.
-- Hence √n ≤ π n, and squaring gives n ≤ π n ^ 2.

open Real Filter Asymptotics

namespace OMA.Erdos4RankinH2

lemma sqrt_mul_log_isLittleO : (fun x : ℝ => √x * log x) =o[atTop] (fun x => x) := by
  have hlog := isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)
  have h2 : (fun x : ℝ => √x * log x) =o[atTop] (fun x : ℝ => √x * x ^ (1 / 2 : ℝ)) :=
    (isBigO_refl (fun x : ℝ => √x) atTop).mul_isLittleO hlog
  refine h2.congr' (EventuallyEq.refl _ _) ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add' hx (by norm_num)]
  norm_num

lemma eventually_two_sqrt_mul_log_le :
    ∀ᶠ x : ℝ in atTop, 2 * (√x * log x) ≤ x * log 2 := by
  have hc : (0 : ℝ) < log 2 / 2 := by positivity
  filter_upwards [sqrt_mul_log_isLittleO.def hc, eventually_ge_atTop 1] with x hx hx1
  rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hx1)),
    Real.norm_of_nonneg (by linarith)] at hx
  linarith

end OMA.Erdos4RankinH2

theorem OMA.solution : OMA.R_Erdos4_erdos_4_variants_rankin_R1.H2 := by
  unfold OMA.R_Erdos4_erdos_4_variants_rankin_R1.H2
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      OMA.Erdos4RankinH2.eventually_two_sqrt_mul_log_le)
  refine ⟨max N 4, fun x hx => ?_⟩
  have hxN : N ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : 4 ≤ x := le_trans (le_max_right _ _) hx
  have key := hN x hxN
  have hx4r : (4 : ℝ) ≤ x := by exact_mod_cast hx4
  have hlogpos : 0 < log (x : ℝ) := Real.log_pos (by linarith)
  -- log (x + 1) ≤ 2 log x
  have hlog1 : log ((x : ℝ) + 1) ≤ 2 * log (x : ℝ) := by
    have hle : (x : ℝ) + 1 ≤ (x : ℝ) ^ 2 := by nlinarith
    calc log ((x : ℝ) + 1) ≤ log ((x : ℝ) ^ 2) := Real.log_le_log (by positivity) hle
      _ = 2 * log (x : ℝ) := by rw [Real.log_pow]; norm_num
  -- 2 ≤ √x
  have hsqrt2 : (2 : ℝ) ≤ √(x : ℝ) := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx4r
  have hsum : √(x : ℝ) * log (x : ℝ) ≤ (x : ℝ) * log 2 - log ((x : ℝ) + 1) := by
    nlinarith
  have hpi := Chebyshev.pi_ge x
  have hsqrt_le : √(x : ℝ) ≤ (Nat.primeCounting x : ℝ) := by
    refine le_trans ?_ hpi
    rw [le_div_iff₀ hlogpos]
    exact hsum
  have hsq : (x : ℝ) ≤ (Nat.primeCounting x : ℝ) ^ 2 := by
    have h0 : 0 ≤ √(x : ℝ) := Real.sqrt_nonneg _
    calc (x : ℝ) = √(x : ℝ) ^ 2 := (Real.sq_sqrt (by positivity)).symm
      _ ≤ (Nat.primeCounting x : ℝ) ^ 2 := pow_le_pow_left₀ h0 hsqrt_le 2
  exact_mod_cast hsq
