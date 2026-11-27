import OMAReductions.R_Erdos1190_erdos_1190_variants_upper_bound_R1
import Mathlib

/-! Split the exponent loss between the initial scale and a summable weight
in the shell index. The fourth Taylor term of the exponential bounds this
weight by a constant multiple of the reciprocal-square series. -/

open Filter Real Finset

private lemma summable_sqrt_weight (d : ℝ) (hd : 0 < d) :
    Summable (fun k : ℕ => exp (-(d * sqrt k))) := by
  apply ((Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left (24 / d^4)).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have h := Real.pow_div_factorial_le_exp (d*sqrt (k : ℝ)) (show 0 ≤ d*sqrt k by positivity) 4
  have hpow : (d*sqrt k)^4 = d^4*(k : ℝ)^2 := by
    rw [mul_pow, show sqrt (k : ℝ)^4 = (sqrt (k : ℝ)^2)^2 by ring, Real.sq_sqrt (by positivity)]
  rw [hpow] at h
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.reduceMul, Nat.cast_mul, Nat.cast_one] at h
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), Real.exp_neg]
  change (exp (d * sqrt k))⁻¹ ≤ 24 / d ^ 4 * (1 / (k : ℝ) ^ 2)
  rw [div_mul_div_comm, mul_one]
  exact (inv_le_comm₀ (exp_pos _) (div_pos (by positivity) (by positivity))).mpr (by
    rw [inv_div]; convert h using 1 <;> norm_num)

theorem OMA.solution : OMA.R_Erdos1190_erdos_1190_variants_upper_bound_R1.H2 := by
  classical
  intro δ hδ hsmall
  let c := δ/4
  let b := sqrt 3/2 - 3*c
  let Z (m : ℕ) := sqrt (log m * log (log m))
  let f (k : ℕ) := exp (-(c*sqrt (log 2)*sqrt k))
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hc : 0 < c := by dsimp [c]; positivity
  have hb : 0 < b := by
    dsimp [b,c]
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sqrt_nonneg (3 : ℝ)]
  have hf : Summable f := summable_sqrt_weight _ (mul_pos hc (sqrt_pos.mpr hl2))
  have hl : Tendsto (fun m : ℕ => log (m : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have big : Tendsto (fun m : ℕ => exp (c*sqrt (log m))) atTop atTop :=
    tendsto_exp_atTop.comp ((tendsto_sqrt_atTop.comp hl).const_mul_atTop hc)
  filter_upwards [big.eventually_gt_atTop (2 * ∑' k, f k),
    (tendsto_log_atTop.comp hl).eventually_ge_atTop 1, hl.eventually_gt_atTop 0,
    eventually_ge_atTop (1 : ℕ)] with m hconst hll hlm hm
  change 1 ≤ log (log (m : ℝ)) at hll
  change 0 < log (m : ℝ) at hlm
  have hZm : sqrt (log m) ≤ Z m := sqrt_le_sqrt (le_mul_of_one_le_right hlm.le hll)
  refine ⟨exp (-b*Z m)*(2*∑' k, f k), ?_, ?_⟩
  · rw [scaleL, ← Real.exp_mul]
    change _ < exp (Z m * (-(sqrt 3 / 2) + δ))
    rw [show Z m * (-(sqrt 3 / 2) + δ) = -b*Z m + c*Z m by dsimp [b,c]; ring, exp_add]
    apply mul_lt_mul_of_pos_left _ (exp_pos _)
    exact hconst.trans_le (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hZm hc.le))
  · intro K
    have pt (k : ℕ) : 2*scaleL (2^(k+1)*m) ^ (-(sqrt 3/2)+δ/2) ≤
        (exp (-b*Z m)*2)*f k := by
      let N := 2^(k+1)*m
      have hn : m ≤ N := Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)
      have hlog : log (N : ℝ) = (k+1)*log 2 + log m := by
        dsimp [N]
        push_cast
        rw [log_mul (by positivity) (by exact_mod_cast (show m ≠ 0 by omega)), log_pow]
        push_cast
        ring
      have hle : log m ≤ log (N : ℝ) := log_le_log (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast hn)
      have hle₂ := log_le_log hlm hle
      have hmono : Z m ≤ Z N := sqrt_le_sqrt (mul_le_mul hle hle₂ (by linarith) (by linarith))
      have hkn : sqrt (log 2) * sqrt k ≤ Z N := by
        rw [← Real.sqrt_mul hl2.le]
        apply sqrt_le_sqrt
        apply le_trans _ (le_mul_of_one_le_right (hlm.le.trans hle) (hll.trans hle₂))
        rw [hlog]
        nlinarith
      rw [scaleL, ← Real.exp_mul]
      change 2*exp (Z N * (-(sqrt 3/2)+δ/2)) ≤ exp (-b*Z m)*2*exp (-(c*sqrt (log 2)*sqrt k))
      rw [mul_comm (exp _) 2, mul_assoc, ← exp_add]
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
      have hde : -(sqrt 3/2)+δ/2 = -b-c := by dsimp [b,c]; ring
      rw [hde]
      nlinarith [mul_le_mul_of_nonneg_left hmono hb.le, mul_le_mul_of_nonneg_left hkn hc.le]
    calc
      _ ≤ ∑ k ∈ range K, (exp (-b*Z m)*2)*f k := sum_le_sum fun k _ => pt k
      _ = (exp (-b*Z m)*2) * ∑ k ∈ range K, f k := (mul_sum ..).symm
      _ ≤ (exp (-b*Z m)*2) * ∑' k, f k := mul_le_mul_of_nonneg_left
        (hf.sum_le_tsum _ (fun k _ => (exp_pos _).le)) (by positivity)
      _ = _ := by ring
