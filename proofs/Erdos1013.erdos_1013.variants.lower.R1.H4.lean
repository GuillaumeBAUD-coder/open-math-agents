import OMAReductions.R_Erdos1013_erdos_1013_variants_lower_R1
import Mathlib

/-! Take `δ = min 1 ε`. If `n < (1/2 - ε) k² log k` and `k ≤ (2+δ) √n / √(log n)`, then
`n ≥ 2` (otherwise the right side is `0`), so `k² log n ≤ (2+δ)² n ≤ 9 n` gives `k² ≤ 14 n` and
`log n ≥ 2 log k - log 14`. Hence `k² (2 log k - log 14) < (2+δ)² (1/2 - ε) k² log k ≤
(2 - ε) k² log k`, i.e. `ε log k < log 14`, which fails for large `k`. -/

open Filter

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_lower_R1.H4 := by
  intro ε hε
  refine ⟨min 1 ε, lt_min one_pos hε, ?_⟩
  have hδ1 : min 1 ε ≤ 1 := min_le_left _ _
  have hδε : min 1 ε ≤ ε := min_le_right _ _
  have hδ0 : 0 < min 1 ε := lt_min one_pos hε
  set δ := min 1 ε with hδ
  have hlog : ∀ᶠ k : ℕ in atTop, Real.log 14 / ε < Real.log k :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  filter_upwards [hlog, eventually_ge_atTop 2] with k hk hk2 n hn
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
  have hk2pos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  by_contra hcon
  push Not at hcon
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases le_or_gt (1 / 2 : ℝ) ε with hεbig | hεsmall
  · have : (1 / 2 - ε) * (k : ℝ) ^ 2 * Real.log k ≤ 0 := by
      have h1 : (1 / 2 - ε) ≤ 0 := by linarith
      have h2 : 0 ≤ (k : ℝ) ^ 2 * Real.log k := by positivity
      nlinarith
    linarith
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have hle : Real.log n ≤ 0 :=
      Real.log_nonpos hn0 (by exact_mod_cast (by omega : n ≤ 1))
    have hs : Real.sqrt (Real.log n) = 0 := Real.sqrt_eq_zero'.mpr hle
    rw [hs, div_zero] at hn
    linarith
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hsq : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.mpr hlogn
  have h1 : (k : ℝ) * Real.sqrt (Real.log n) ≤ (2 + δ) * Real.sqrt n := by
    rwa [le_div_iff₀ hsq] at hn
  have h2 : (k : ℝ) ^ 2 * Real.log n ≤ (2 + δ) ^ 2 * n := by
    have h0 : 0 ≤ (k : ℝ) * Real.sqrt (Real.log n) := by positivity
    have := mul_self_le_mul_self h0 h1
    have e1 : (k : ℝ) * Real.sqrt (Real.log n) * ((k : ℝ) * Real.sqrt (Real.log n)) =
        (k : ℝ) ^ 2 * Real.log n := by
      rw [show (k : ℝ) * Real.sqrt (Real.log n) * ((k : ℝ) * Real.sqrt (Real.log n)) =
        (k : ℝ) ^ 2 * (Real.sqrt (Real.log n) * Real.sqrt (Real.log n)) by ring,
        Real.mul_self_sqrt hlogn.le]
    have e2 : (2 + δ) * Real.sqrt n * ((2 + δ) * Real.sqrt n) = (2 + δ) ^ 2 * n := by
      rw [show (2 + δ) * Real.sqrt n * ((2 + δ) * Real.sqrt n) =
        (2 + δ) ^ 2 * (Real.sqrt n * Real.sqrt n) by ring, Real.mul_self_sqrt hn0]
    rw [e1, e2] at this
    exact this
  have hl2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogn2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have h9 : (2 + δ) ^ 2 ≤ 9 := by nlinarith
  have hn14 : (k : ℝ) ^ 2 ≤ 14 * n := by
    have h3 : (k : ℝ) ^ 2 * 0.69 ≤ (k : ℝ) ^ 2 * Real.log n := by
      apply mul_le_mul_of_nonneg_left _ hk2pos.le; linarith
    have h4 : (2 + δ) ^ 2 * (n : ℝ) ≤ 9 * n := mul_le_mul_of_nonneg_right h9 hn0
    nlinarith
  have hlogn3 : 2 * Real.log k - Real.log 14 ≤ Real.log n := by
    have := Real.log_le_log hk2pos hn14
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
    push_cast at this
    linarith
  have hδsq : δ ^ 2 ≤ δ := by nlinarith
  have hcoef : (2 + δ) ^ 2 * (1 / 2 - ε) ≤ 2 - ε := by
    have e : (2 + δ) ^ 2 * (1 / 2 - ε) = 2 - 4 * ε + 2 * δ + δ ^ 2 / 2 - 4 * (δ * ε) - δ ^ 2 * ε := by
      ring
    rw [e]
    have h1 : 0 ≤ δ * ε := mul_nonneg hδ0.le hε.le
    have h2 : 0 ≤ δ ^ 2 * ε := mul_nonneg (sq_nonneg δ) hε.le
    linarith
  have h3 : (k : ℝ) ^ 2 * (2 * Real.log k - Real.log 14) ≤ (2 + δ) ^ 2 * n :=
    le_trans (mul_le_mul_of_nonneg_left hlogn3 hk2pos.le) h2
  have h4 : (2 + δ) ^ 2 * (n : ℝ) < (2 + δ) ^ 2 * ((1 / 2 - ε) * (k : ℝ) ^ 2 * Real.log k) :=
    mul_lt_mul_of_pos_left hcon (by positivity)
  have h5 : (2 + δ) ^ 2 * ((1 / 2 - ε) * (k : ℝ) ^ 2 * Real.log k) ≤
      (2 - ε) * ((k : ℝ) ^ 2 * Real.log k) := by
    have := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ (k : ℝ) ^ 2 * Real.log k)
    linarith [this]
  have h6 : (k : ℝ) ^ 2 * (ε * Real.log k - Real.log 14) < 0 := by nlinarith
  have h7 : ε * Real.log k - Real.log 14 < 0 := by
    by_contra h
    push Not at h
    have := mul_nonneg hk2pos.le h
    linarith
  have h8 : Real.log 14 < ε * Real.log k := by
    rw [div_lt_iff₀ hε] at hk
    linarith
  linarith
