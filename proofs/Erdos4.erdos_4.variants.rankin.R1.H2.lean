import OMAReductions.R_Erdos4_erdos_4_variants_rankin_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

-- Step Erdos4.erdos_4.variants.rankin.R1.H2: hypothesis H2 of reduction Erdos4.erdos_4.variants.rankin.R1
-- Credit: @DeepDuke
-- H2 := ∃ N : ℕ, ∀ x : ℕ, N ≤ x → x ≤ Nat.primeCounting x ^ 2

theorem OMA.solution : OMA.R_Erdos4_erdos_4_variants_rankin_R1.H2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := (isLittleO_log_rpow_atTop (r := (1 : ℝ)/2) (by norm_num)).bound
    (show 0 < Real.log 2 / 4 by positivity)
  have hn := Filter.Tendsto.eventually tendsto_natCast_atTop_atTop hb
  have hev : ∀ᶠ x : ℕ in Filter.atTop, x ≤ Nat.primeCounting x ^ 2 := by
    filter_upwards [hn, Filter.eventually_ge_atTop (4 : ℕ)] with x hlog hx
    have hx0 : (0 : ℝ) ≤ x := by positivity
    have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
    have hx4 : (4 : ℝ) ≤ x := by exact_mod_cast hx
    have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
    have hspos : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hsq : (Real.sqrt (x : ℝ))^2 = x := Real.sq_sqrt hx0
    have hsle : Real.sqrt (x : ℝ) ≤ x := by nlinarith
    have hl : Real.log (x : ℝ) ≤ Real.log 2 / 4 * Real.sqrt (x : ℝ) := by
      simpa only [Real.norm_eq_abs, abs_of_pos hlogpos, Real.sqrt_eq_rpow,
        abs_of_nonneg (Real.rpow_nonneg hx0 _)] using hlog
    have hladd : Real.log ((x : ℝ)+1) ≤ Real.log 2 + Real.log x := by
      calc
        _ ≤ Real.log (2*(x : ℝ)) := Real.log_le_log (by positivity) (by linarith)
        _ = _ := Real.log_mul (by norm_num) (by positivity)
    have hlerr : Real.log ((x : ℝ)+1) ≤ (x : ℝ)*Real.log 2/2 := by
      have h1 := mul_le_mul_of_nonneg_left hsle (show 0 ≤ Real.log 2/4 by positivity)
      have h2 := mul_le_mul_of_nonneg_right hx4 hlog2.le
      linarith
    have hc := Chebyshev.pi_ge x
    have hlow : (x : ℝ)*Real.log 2/2 ≤ (Nat.primeCounting x : ℝ)*Real.log x := by
      have h := (div_le_iff₀ hlogpos).mp hc
      linarith
    have hupper := mul_le_mul_of_nonneg_left hl
      (show 0 ≤ (Nat.primeCounting x : ℝ) by positivity)
    have hprod : 2*(x : ℝ) ≤ (Nat.primeCounting x : ℝ)*Real.sqrt x := by
      apply (mul_le_mul_iff_right₀ hlog2).mp
      nlinarith only [hlow, hupper]
    have hs : Real.sqrt (x : ℝ) ≤ Nat.primeCounting x := by
      apply (mul_le_mul_iff_left₀ hspos).mp
      nlinarith only [hprod, hsq, hx0]
    have hfinal : (x : ℝ) ≤ (Nat.primeCounting x : ℝ)^2 := by
      nlinarith [Real.sqrt_nonneg (x : ℝ)]
    exact_mod_cast hfinal
  exact Filter.eventually_atTop.mp hev

