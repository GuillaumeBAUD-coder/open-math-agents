import FormalConjectures.OEIS.«38098»

-- Reduction OeisA38098.conjecture1.R1 of Number of primes $< n^3$ — conjecture1
-- Credit: @senamakel
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Route: write x = n^k, y = (n+1)^k and D(x) = li(x) - x/log x. Since li(y) - li(x) is at most
-- (y - x)/log x, if |pi(x) - li(x)| <= E(x), |pi(y) - li(y)| <= E(y) and
-- (1 - x/y) D(x)/x > E(x)/x + E(y)/y, then pi(y)/y < pi(x)/x (ratio_lt_of_bounds). Integration
-- by parts gives D(x) >= (x - 2)/log^2 x - 2.886. With Schoenfeld's error term
-- E(t) = sqrt t log t/(8 pi) (H2, a consequence of RH, H1) and Bernoulli's 1 - x/y >= k/(n+k),
-- the criterion holds for every k >= 4 with n^k >= 10^10 (tail) and for k = 3 with n >= 10^7
-- (tail_three). The remaining pairs are the finite checks H3 (n^k < 10^10) and H4 (k = 3,
-- 10^10 <= n^3, n < 10^7), where Schoenfeld's bound is too weak for k = 3.
--
-- H1: the Riemann hypothesis (Mathlib RiemannHypothesis).
-- H2: under RH, Schoenfeld 1976, Corollary 1: |pi(x) - li(x)| < sqrt x log x/(8 pi) for real
--     x >= 2657, with pi(x) = pi(floor x) and li the principal-value logarithmic integral
--     (Real.logIntegral of formal-conjectures).
-- H3: the finite check: the inequality for every k > 2, n >= 2 with n^k < 10^10.
-- H4: the finite check for k = 3 and 10^10 <= n^3, n < 10^7 (that is 2155 <= n < 10^7).

namespace OMA.R_OeisA38098_conjecture1_R1

open Real

def H1 : Prop := RiemannHypothesis

def H2 : Prop :=
  RiemannHypothesis → ∀ x : ℝ, 2657 ≤ x →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logIntegral x|
      < 1 / (8 * Real.pi) * (Real.sqrt x * Real.log x)

def H3 : Prop :=
  ∀ k : ℕ, 2 < k → ∀ n : ℕ, 2 ≤ n → n ^ k < 10 ^ 10 →
    (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ) <
    (Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ)

def H4 : Prop :=
  ∀ n : ℕ, 10 ^ 10 ≤ n ^ 3 → n < 10 ^ 7 →
    (Nat.primeCounting ((n + 1) ^ 3) : ℚ) / ((n + 1) ^ 3 : ℚ) <
    (Nat.primeCounting (n ^ 3) : ℚ) / (n ^ 3 : ℚ)

theorem logIntegralTwo_nonneg' : 0 ≤ Real.logIntegralTwo := by
  have := Real.logIntegral_two_pos
  rw [Real.logIntegral_two] at this
  exact this.le

theorem logIntegralTwo_le_two' : Real.logIntegralTwo ≤ 2 := by
  unfold Real.logIntegralTwo
  calc ∫ u in Set.Ioo (0 : ℝ) 1, (1 / Real.log (1 + u) + 1 / Real.log (1 - u))
      ≤ ∫ u in Set.Ioo (0 : ℝ) 1, (2 : ℝ) :=
        MeasureTheory.setIntegral_mono_on Real.logIntegralTwo_integrand_integrableOn
          (MeasureTheory.integrableOn_const (hs := by simp) (hC := by simp)) measurableSet_Ioo
          (fun u hu => Real.logIntegralTwo_integrand_le_two hu.1 hu.2)
    _ = 2 := by simp

/-- `|2/log 2 − li(2)| ≤ 2.886`. -/
theorem pi_const_bound : |2 / Real.log 2 - Real.logIntegralTwo| ≤ 2.886 := by
  have hli2 := logIntegralTwo_nonneg'
  have hli2' := logIntegralTwo_le_two'
  have hlog2 := Real.log_two_gt_d9
  have h2l : 2 / Real.log 2 ≤ 2.886 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have h2l' : 2 ≤ 2 / Real.log 2 := by
    rw [le_div_iff₀ (by linarith)]; linarith [Real.log_two_lt_d9]
  rw [abs_le]; constructor <;> linarith

theorem continuousOn_inv_log_pow {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (n : ℕ) :
    ContinuousOn (fun t : ℝ => 1 / Real.log t ^ n) (Set.uIcc a b) := by
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl : Real.log t ^ n ≠ 0 := pow_ne_zero _ (Real.log_pos (by linarith [ht.1])).ne'
  exact (continuousAt_const.div ((Real.continuousAt_log ht0).pow n) hl).continuousWithinAt

/-- Integration by parts: `li(x) = li(2) + x/log x − 2/log 2 + ∫₂ˣ dt/log² t`. -/
theorem logIntegral_eq_parts {x : ℝ} (hx : 2 ≤ x) :
    Real.logIntegral x = Real.logIntegralTwo + x / Real.log x - 2 / Real.log 2
      + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
  have i1 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 1) MeasureTheory.volume 2 x :=
    (continuousOn_inv_log_pow le_rfl hx 1).intervalIntegrable
  have i2 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) MeasureTheory.volume 2 x :=
    (continuousOn_inv_log_pow le_rfl hx 2).intervalIntegrable
  have hFTC : ∫ t in (2 : ℝ)..x, (1 / Real.log t ^ 1 - 1 / Real.log t ^ 2)
      = x / Real.log x - 2 / Real.log 2 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => t / Real.log t)
      (fun t ht => ?_) (i1.sub i2)
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl := (Real.log_pos (show (1 : ℝ) < t by linarith [ht.1])).ne'
    have h' : HasDerivAt (fun t => t / Real.log t)
        ((1 * Real.log t - t * t⁻¹) / Real.log t ^ 2) t :=
      (hasDerivAt_id' t).div (Real.hasDerivAt_log ht0) hl
    refine h'.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_sub i1 i2] at hFTC
  simp only [pow_one] at hFTC
  unfold Real.logIntegral
  linarith

theorem intervalIntegrable_inv_log {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [Set.mem_uIcc] at ht
  have h1 : 1 < t := by rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  apply ContinuousAt.continuousWithinAt
  exact continuousAt_const.div (Real.continuousAt_log (by linarith)) (Real.log_pos h1).ne'

theorem integral_inv_log_bounds {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (b - a) / Real.log b ≤ ∫ t in a..b, 1 / Real.log t ∧
      ∫ t in a..b, 1 / Real.log t ≤ (b - a) / Real.log a := by
  have hII := intervalIntegrable_inv_log ha (by linarith : 1 < b)
  have hla := Real.log_pos ha
  constructor
  · have := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := 1 / Real.log b))
      hII (fun t ht => one_div_le_one_div_of_le (Real.log_pos (by linarith [ht.1]))
        (Real.log_le_log (by linarith [ht.1]) ht.2))
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    rw [div_eq_mul_one_div]; exact this
  · have := intervalIntegral.integral_mono_on hab hII
      (intervalIntegrable_const (c := 1 / Real.log a))
      (fun t ht => one_div_le_one_div_of_le hla (Real.log_le_log (by linarith) ht.1))
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    rw [div_eq_mul_one_div]; exact this

theorem logIntegral_eq_add {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    Real.logIntegral b = Real.logIntegral a + ∫ t in a..b, 1 / Real.log t := by
  unfold Real.logIntegral
  rw [add_assoc, intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_inv_log (by norm_num) (by linarith))
    (intervalIntegrable_inv_log (by linarith) (by linarith))]

/-- `D(x) = li(x) − x/log x ≥ (x − 2)/log² x − 2.886` for `x ≥ 2`. -/
theorem logIntegral_sub_ge {x : ℝ} (hx : 2 ≤ x) :
    (x - 2) / Real.log x ^ 2 - 2.886 ≤ logIntegral x - x / Real.log x := by
  rw [logIntegral_eq_parts hx]
  have hc := abs_le.mp pi_const_bound
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hI : (x - 2) / Real.log x ^ 2 ≤ ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
    have hmono : ∫ t in (2 : ℝ)..x, (1 / Real.log x ^ 2) ≤ ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
      refine intervalIntegral.integral_mono_on hx intervalIntegrable_const
        (continuousOn_inv_log_pow le_rfl hx 2).intervalIntegrable (fun t ht => ?_)
      have ht2 : 2 ≤ t := ht.1
      have hlt : 0 < Real.log t := Real.log_pos (by linarith)
      have hle : Real.log t ≤ Real.log x := Real.log_le_log (by linarith) ht.2
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hlt.le hle 2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    calc (x - 2) / Real.log x ^ 2 = (x - 2) * (1 / Real.log x ^ 2) := by ring
      _ ≤ _ := hmono
  linarith [hc.1, hc.2]

/-- `li(y) − li(x) ≤ (y − x)/log x` for `2 ≤ x ≤ y`. -/
theorem logIntegral_sub_le {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    logIntegral y - logIntegral x ≤ (y - x) / Real.log x := by
  rw [logIntegral_eq_add hx (hx.trans hxy)]
  have := (integral_inv_log_bounds (a := x) (b := y) (by linarith) hxy).2
  linarith

/-- **The comparison.** If `π(x)`, `π(y)` are within `Ex`, `Ey` of `li`, `Dl ≤ li(x) − x/log x`
and `(1 − x/y)·Dl/x > Ex/x + Ey/y`, then `π(y)/y < π(x)/x`. -/
theorem ratio_lt_of_bounds {x y Px Py Ex Ey Dl : ℝ} (hx : 2 ≤ x) (hxy : x < y)
    (hPx : |Px - logIntegral x| ≤ Ex) (hPy : |Py - logIntegral y| ≤ Ey)
    (hD : Dl ≤ logIntegral x - x / Real.log x)
    (hkey : Ex / x + Ey / y < (1 - x / y) * Dl / x) :
    Py / y < Px / x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hli := logIntegral_sub_le hx hxy.le
  set A := logIntegral x - x / Real.log x with hA
  have hPy' : Py ≤ logIntegral y + Ey := by linarith [(abs_le.mp hPy).2]
  have hPx' : logIntegral x - Ex ≤ Px := by linarith [(abs_le.mp hPx).1]
  -- `Py ≤ y/log x + A + Ey`
  have h1 : Py ≤ y / Real.log x + A + Ey := by
    have : y / Real.log x = x / Real.log x + (y - x) / Real.log x := by ring
    rw [this, hA]; linarith
  -- `Px ≥ x/log x + A − Ex`
  have h2 : x / Real.log x + A - Ex ≤ Px := by rw [hA]; linarith
  have e1 : (y / Real.log x + A + Ey) / y = 1 / Real.log x + A / y + Ey / y := by
    field_simp
  have e2 : (x / Real.log x + A - Ex) / x = 1 / Real.log x + A / x - Ex / x := by
    field_simp
  have hkey' : (1 - x / y) * Dl / x = Dl / x - Dl / y := by field_simp
  have hxy' : 1 / y ≤ 1 / x := one_div_le_one_div_of_le hx0 hxy.le
  have hAD : Dl * (1 / x - 1 / y) ≤ A * (1 / x - 1 / y) :=
    mul_le_mul_of_nonneg_right hD (by linarith)
  have e3 : Dl * (1 / x - 1 / y) = Dl / x - Dl / y := by ring
  have e4 : A * (1 / x - 1 / y) = A / x - A / y := by ring
  calc Py / y ≤ (y / Real.log x + A + Ey) / y := div_le_div_of_nonneg_right h1 hy0.le
    _ = 1 / Real.log x + A / y + Ey / y := e1
    _ < 1 / Real.log x + A / x - Ex / x := by linarith
    _ = (x / Real.log x + A - Ex) / x := e2.symm
    _ ≤ Px / x := div_le_div_of_nonneg_right h2 hx0.le

/-- `log t/√t` decreases on `[e², ∞)`: `log y/√y ≤ log x/√x` for `x ≤ y`, `log x ≥ 2`. -/
theorem log_div_sqrt_anti {x y : ℝ} (hx0 : 0 < x) (hx : 2 ≤ Real.log x) (hxy : x ≤ y) :
    Real.log y / √y ≤ Real.log x / √x := by
  have hy0 : 0 < y := hx0.trans_le hxy
  set r := y / x with hr
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ hx0]; linarith
  have hyr : y = x * r := by rw [hr]; field_simp
  have hsr : 1 ≤ √r := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hr1
  have hlogr : Real.log r ≤ 2 * (√r - 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < √r by linarith)
    have : Real.log r = 2 * Real.log √r := by
      rw [← Real.log_rpow (by linarith), show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast, Real.sq_sqrt (by linarith)]
    linarith
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx0
  have hsy : √y = √x * √r := by rw [hyr, Real.sqrt_mul hx0.le]
  have hly : Real.log y = Real.log x + Real.log r := by
    rw [hyr, Real.log_mul hx0.ne' (by linarith)]
  rw [hsy, hly, div_le_div_iff₀ (by positivity) hsx]
  have : Real.log r ≤ Real.log x * (√r - 1) := by nlinarith
  have hlx : 0 ≤ Real.log x := by linarith
  nlinarith [mul_le_mul_of_nonneg_left this hsx.le]

/-- `log w ≤ w/e` for `w > 0`. -/
lemma log_le_div_exp_one {w : ℝ} (hw : 0 < w) : Real.log w ≤ w / Real.exp 1 := by
  have h := Real.add_one_le_exp (Real.log w - 1)
  rw [Real.exp_sub, Real.exp_log hw] at h
  linarith

/-- The polynomial inequality behind the tail. -/
lemma tail_poly {w : ℝ} (hw : 2.053 ≤ w) :
    46.18 * π * (11.773 * w) ^ 2 + (w ^ 8) ^ 2 * (11.773 * w) ^ 3 * (w ^ 8 + 4)
      < 16 * π * (w ^ 32 - 2) := by
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have hw0 : 0 ≤ w := by linarith
  have h2 : (4.2148 : ℝ) ≤ w ^ 2 := by nlinarith
  have h4 : (17.764 : ℝ) ≤ w ^ 4 := by nlinarith
  have h5 : (36.4 : ℝ) ≤ w ^ 5 := by
    have : w ^ 5 = w ^ 4 * w := by ring
    rw [this]; nlinarith
  have h8 : (315 : ℝ) ≤ w ^ 8 := by
    have : w ^ 8 = w ^ 4 * w ^ 4 := by ring
    rw [this]; nlinarith
  have h19 : (1 : ℝ) ≤ w ^ 19 := one_le_pow₀ (by linarith)
  have hw2 : w ^ 2 ≤ w ^ 19 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h19p : 0 ≤ w ^ 19 := by positivity
  have h27p : 0 ≤ w ^ 27 := by positivity
  have e32 : w ^ 32 = w ^ 5 * w ^ 27 := by ring
  have e27 : w ^ 27 = w ^ 8 * w ^ 19 := by ring
  have hA : 36.4 * w ^ 27 ≤ w ^ 32 := by rw [e32]; exact mul_le_mul_of_nonneg_right h5 h27p
  have hB : 315 * w ^ 19 ≤ w ^ 27 := by rw [e27]; exact mul_le_mul_of_nonneg_right h8 h19p
  have eL : 46.18 * π * (11.773 * w) ^ 2 + (w ^ 8) ^ 2 * (11.773 * w) ^ 3 * (w ^ 8 + 4)
      = 46.18 * 11.773 ^ 2 * π * w ^ 2 + 11.773 ^ 3 * w ^ 27 + 4 * 11.773 ^ 3 * w ^ 19 := by ring
  rw [eL]
  nlinarith

/-- **The tail inequality.** For `x ≥ 10¹⁰`,
`2 (√x log x/(8π)) (x^{1/4} + 4) < 4 ((x − 2)/log² x − 2.886)`. -/
theorem tail_core {x : ℝ} (hx : 10 ^ 10 ≤ x) :
    2 * (1 / (8 * π) * (√x * Real.log x)) * (√(√x) + 4)
      < 4 * ((x - 2) / Real.log x ^ 2 - 2.886) := by
  have hx0 : 0 < x := by linarith
  set s := √(√x) with hs
  set w := √(√(√s)) with hw
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hsx : s ^ 2 = √x := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hx4 : s ^ 4 = x := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hsx, Real.sq_sqrt hx0.le]
  have hws : w ^ 8 = s := by
    have a1 : w ^ 2 = √(√s) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have a2 : (√(√s)) ^ 2 = √s := Real.sq_sqrt (Real.sqrt_nonneg _)
    have a3 : (√s) ^ 2 = s := Real.sq_sqrt hs0
    rw [show w ^ 8 = ((w ^ 2) ^ 2) ^ 2 by ring, a1, a2, a3]
  have hxw : x = w ^ 32 := by rw [← hx4, ← hws]; ring
  -- `s > 316`, so `w > 2.053`
  have hs316 : 316 < s := by
    by_contra h; push Not at h
    have : s ^ 4 ≤ (316 : ℝ) ^ 4 := pow_le_pow_left₀ hs0 h 4
    rw [hx4] at this; norm_num at this; linarith
  have hw2 : 2.053 ≤ w := by
    by_contra h; push Not at h
    have : w ^ 8 ≤ (2.053 : ℝ) ^ 8 := pow_le_pow_left₀ hw0 h.le 8
    rw [hws] at this; norm_num at this; linarith
  have hwpos : 0 < w := by linarith
  -- `log x ≤ 11.773 w`
  have hLw : Real.log x = 32 * Real.log w := by rw [hxw, Real.log_pow]; push_cast; ring
  have he := Real.exp_one_gt_d9
  have hL : Real.log x ≤ 11.773 * w := by
    have h1 := log_le_div_exp_one hwpos
    have h2 : w / Real.exp 1 ≤ w / 2.7182818283 :=
      div_le_div_of_nonneg_left hw0 (by norm_num) he.le
    have h3 : w / 2.7182818283 ≤ 0.36788 * w := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    rw [hLw]; linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  set L := Real.log x
  set Λ := 11.773 * w with hΛ
  have hΛ0 : 0 < Λ := by positivity
  have hpi := Real.pi_pos
  -- replace `L` by `Λ` on both sides
  have hlhs : 2 * (1 / (8 * π) * (√x * L)) * (s + 4) ≤ 2 * (1 / (8 * π) * (√x * Λ)) * (s + 4) := by
    have : √x * L ≤ √x * Λ := mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg _)
    have h8 : 0 ≤ 1 / (8 * π) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h8]
  have hrhs : (x - 2) / Λ ^ 2 ≤ (x - 2) / L ^ 2 :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) (pow_le_pow_left₀ hL0.le hL 2)
  have hP := tail_poly hw2
  -- the polynomial inequality, divided by `4π Λ²`
  rw [hws, ← hxw, ← hΛ] at hP
  have hmain : 2 * (1 / (8 * π) * (√x * Λ)) * (s + 4) < 4 * ((x - 2) / Λ ^ 2 - 2.886) := by
    rw [← hsx]
    have hΛ2 : 0 < Λ ^ 2 := by positivity
    have e1 : 2 * (1 / (8 * π) * (s ^ 2 * Λ)) * (s + 4) = s ^ 2 * Λ ^ 3 * (s + 4) / (4 * π * Λ ^ 2) := by
      field_simp; ring
    have e2 : 4 * ((x - 2) / Λ ^ 2 - 2.886) = (16 * π * (x - 2) - 46.176 * π * Λ ^ 2) / (4 * π * Λ ^ 2) := by
      field_simp; ring
    rw [e1, e2]
    apply div_lt_div_of_pos_right _ (by positivity)
    nlinarith [mul_pos hpi hΛ2]
  calc 2 * (1 / (8 * π) * (√x * L)) * (s + 4) ≤ _ := hlhs
    _ < _ := hmain
    _ ≤ 4 * ((x - 2) / L ^ 2 - 2.886) := by linarith

/-- `1 − n^k/(n+1)^k ≥ k/(n+k)` (Bernoulli). -/
lemma one_sub_ratio_ge (n k : ℕ) (hn : 1 ≤ n) :
    (k : ℝ) / (n + k) ≤ 1 - (n : ℝ) ^ k / ((n : ℝ) + 1) ^ k := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hB : 1 + (k : ℝ) * (1 / n) ≤ (1 + 1 / n) ^ k :=
    one_add_mul_le_pow (by have : 0 ≤ 1 / (n : ℝ) := by positivity
                           linarith) k
  have hy : ((n : ℝ) + 1) ^ k = (n : ℝ) ^ k * (1 + 1 / n) ^ k := by
    rw [← mul_pow]; congr 1; field_simp
  have hxk : (0 : ℝ) < (n : ℝ) ^ k := by positivity
  have hpos : (0 : ℝ) < 1 + k * (1 / n) := by positivity
  have hle : (n : ℝ) ^ k / ((n : ℝ) + 1) ^ k ≤ 1 / (1 + k * (1 / n)) := by
    rw [hy, div_le_div_iff₀ (by positivity) hpos]
    nlinarith
  have e : 1 / (1 + (k : ℝ) * (1 / n)) = 1 - k / (n + k) := by
    field_simp; ring
  linarith

/-- **The tail.** For `k ≥ 4`, `n ≥ 2` and `n^k ≥ 10¹⁰`, Schoenfeld's bound gives
`π((n+1)^k)/(n+1)^k < π(n^k)/n^k`. -/
theorem tail (hS : ∀ x : ℝ, 2657 ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logIntegral x| < 1 / (8 * π) * (√x * Real.log x)) {k n : ℕ} (hk : 4 ≤ k) (hn : 2 ≤ n) (hx : 10 ^ 10 ≤ n ^ k) :
    (Nat.primeCounting ((n + 1) ^ k) : ℝ) / (((n + 1) ^ k : ℕ) : ℝ) <
      (Nat.primeCounting (n ^ k) : ℝ) / ((n ^ k : ℕ) : ℝ) := by
  set x : ℝ := ((n ^ k : ℕ) : ℝ) with hxdef
  set y : ℝ := (((n + 1) ^ k : ℕ) : ℝ) with hydef
  have hxR : (10 : ℝ) ^ 10 ≤ x := by rw [hxdef]; exact_mod_cast hx
  have hx0 : 0 < x := by linarith
  have hxy : x < y := by
    rw [hxdef, hydef]; exact_mod_cast Nat.pow_lt_pow_left (by omega) (by omega)
  have hy0 : 0 < y := by linarith
  have hfx : ⌊x⌋₊ = n ^ k := Nat.floor_natCast _
  have hfy : ⌊y⌋₊ = (n + 1) ^ k := Nat.floor_natCast _
  have hSx := hS x (by linarith)
  have hSy := hS y (by linarith)
  rw [hfx] at hSx
  rw [hfy] at hSy
  have hlx : 2 ≤ Real.log x := by
    have := Real.add_one_le_exp (2 : ℝ)
    have h7 : Real.exp 2 ≤ x := by
      have : Real.exp 2 < 8 := by
        have := Real.exp_one_lt_d9
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith [Real.exp_pos 1]
      linarith
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) h7
  set Ex := 1 / (8 * π) * (√x * Real.log x)
  set Ey := 1 / (8 * π) * (√y * Real.log y)
  set Dl := (x - 2) / Real.log x ^ 2 - 2.886
  have hpi := Real.pi_pos
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx0
  have hsy : 0 < √y := Real.sqrt_pos.mpr hy0
  -- `Ey/y ≤ Ex/x`
  have hEx : Ex / x = 1 / (8 * π) * (Real.log x / √x) := by
    have h : √x * Real.log x / x = Real.log x / √x := by
      rw [div_eq_div_iff hx0.ne' hsx.ne']
      have := Real.mul_self_sqrt hx0.le
      linear_combination Real.log x * this
    simp only [Ex]; rw [mul_div_assoc, h]
  have hEy : Ey / y = 1 / (8 * π) * (Real.log y / √y) := by
    have h : √y * Real.log y / y = Real.log y / √y := by
      rw [div_eq_div_iff hy0.ne' hsy.ne']
      have := Real.mul_self_sqrt hy0.le
      linear_combination Real.log y * this
    simp only [Ey]; rw [mul_div_assoc, h]
  have hmono : Ey / y ≤ Ex / x := by
    rw [hEx, hEy]
    exact mul_le_mul_of_nonneg_left (log_div_sqrt_anti hx0 hlx hxy.le) (by positivity)
  -- `1 − x/y ≥ 4/(s + 4)`
  set s := √(√x)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hns : (n : ℝ) ≤ s := by
    have h4 : (n : ℝ) ^ 4 ≤ x := by
      rw [hxdef]; push_cast
      exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ n by omega)) hk
    have hsx4 : s ^ 4 = x := by
      have : s ^ 2 = √x := Real.sq_sqrt (Real.sqrt_nonneg _)
      rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, this, Real.sq_sqrt hx0.le]
    rw [← hsx4] at h4
    exact (pow_le_pow_iff_left₀ (by positivity) hs0 (by norm_num)).mp h4
  have hratio : 4 / (s + 4) ≤ 1 - x / y := by
    have h1 := one_sub_ratio_ge n k (by omega)
    have e : x / y = (n : ℝ) ^ k / ((n : ℝ) + 1) ^ k := by rw [hxdef, hydef]; push_cast; ring
    rw [e]
    refine le_trans ?_ h1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hcore := tail_core hxR
  have hDl : 0 < Dl := by
    have : 0 < 2 * Ex * (s + 4) := by positivity
    simp only [Dl]; nlinarith
  have hkey : Ex / x + Ey / y < (1 - x / y) * Dl / x := by
    have h1 : 2 * Ex * (s + 4) < 4 * Dl := hcore
    have h2 : 2 * (Ex / x) < 4 / (s + 4) * Dl / x := by
      rw [div_mul_eq_mul_div, div_div, lt_div_iff₀ (by positivity)]
      have e : 2 * (Ex / x) * ((s + 4) * x) = 2 * Ex * (s + 4) := by field_simp
      rw [e]; linarith
    have h3 : 4 / (s + 4) * Dl / x ≤ (1 - x / y) * Dl / x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hratio hDl.le) hx0.le
    linarith
  exact ratio_lt_of_bounds (by linarith) hxy hSx.le hSy.le (logIntegral_sub_ge (by linarith)) hkey

/-- The polynomial inequality behind the `k = 3` tail. -/
lemma tail3_poly {w : ℝ} (hw : 2.738 ≤ w) (h16 : 10 ^ 7 ≤ w ^ 16) :
    34.632 * π * (17.659 * w) ^ 2 + w ^ 24 * (17.659 * w) ^ 3 * (w ^ 16 + 3)
      < 12 * π * (w ^ 48 - 2) := by
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have hw0 : 0 ≤ w := by linarith
  have h2 : (7.4966 : ℝ) ≤ w ^ 2 := by nlinarith
  have h4 : (56.199 : ℝ) ≤ w ^ 4 := by
    have : w ^ 4 = w ^ 2 * w ^ 2 := by ring
    rw [this]; nlinarith
  have h5 : (153 : ℝ) ≤ w ^ 5 := by
    have : w ^ 5 = w ^ 4 * w := by ring
    rw [this]; nlinarith
  have h27 : (1 : ℝ) ≤ w ^ 27 := one_le_pow₀ (by linarith)
  have hw2 : w ^ 2 ≤ w ^ 27 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h27p : 0 ≤ w ^ 27 := by positivity
  have h43p : 0 ≤ w ^ 43 := by positivity
  have e48 : w ^ 48 = w ^ 5 * w ^ 43 := by ring
  have e43 : w ^ 43 = w ^ 16 * w ^ 27 := by ring
  have hA : 153 * w ^ 43 ≤ w ^ 48 := by rw [e48]; exact mul_le_mul_of_nonneg_right h5 h43p
  have hB : 10 ^ 7 * w ^ 27 ≤ w ^ 43 := by rw [e43]; exact mul_le_mul_of_nonneg_right h16 h27p
  have eL : 34.632 * π * (17.659 * w) ^ 2 + w ^ 24 * (17.659 * w) ^ 3 * (w ^ 16 + 3)
      = 34.632 * 17.659 ^ 2 * π * w ^ 2 + 17.659 ^ 3 * w ^ 43 + 3 * 17.659 ^ 3 * w ^ 27 := by
    ring
  rw [eL]
  nlinarith

/-- **The `k = 3` tail inequality.** For `m ≥ 10⁷`, with `x = m³`,
`2 (√x log x/(8π)) (m + 3) < 3 ((x − 2)/log² x − 2.886)`. -/
theorem tail3_core {m : ℝ} (hm : 10 ^ 7 ≤ m) :
    2 * (1 / (8 * π) * (√(m ^ 3) * Real.log (m ^ 3))) * (m + 3)
      < 3 * ((m ^ 3 - 2) / Real.log (m ^ 3) ^ 2 - 2.886) := by
  have hm0 : 0 < m := by linarith
  have hm3 : (10 : ℝ) ^ 7 ≤ m ^ 3 :=
    calc (10 : ℝ) ^ 7 ≤ m := hm
      _ = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  set w := √(√(√(√m))) with hw
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hwm : w ^ 16 = m := by
    have a1 : w ^ 2 = √(√(√m)) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have a2 : (√(√(√m))) ^ 2 = √(√m) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have a3 : (√(√m)) ^ 2 = √m := Real.sq_sqrt (Real.sqrt_nonneg _)
    have a4 : (√m) ^ 2 = m := Real.sq_sqrt hm0.le
    rw [show w ^ 16 = (((w ^ 2) ^ 2) ^ 2) ^ 2 by ring, a1, a2, a3, a4]
  have hx : m ^ 3 = w ^ 48 := by rw [← hwm]; ring
  have hsx : √(m ^ 3) = w ^ 24 := by
    rw [hx, show w ^ 48 = (w ^ 24) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have h16 : (10 : ℝ) ^ 7 ≤ w ^ 16 := by rw [hwm]; exact hm
  have hw2 : 2.738 ≤ w := by
    by_contra h; push Not at h
    have : w ^ 16 ≤ (2.738 : ℝ) ^ 16 := pow_le_pow_left₀ hw0 h.le 16
    norm_num at this; linarith
  have hwpos : 0 < w := by linarith
  have hLw : Real.log (m ^ 3) = 48 * Real.log w := by rw [hx, Real.log_pow]; push_cast; ring
  have he := Real.exp_one_gt_d9
  have hL : Real.log (m ^ 3) ≤ 17.659 * w := by
    have h1 := log_le_div_exp_one hwpos
    have h2 : w / Real.exp 1 ≤ w / 2.7182818283 :=
      div_le_div_of_nonneg_left hw0 (by norm_num) he.le
    have h3 : w / 2.7182818283 ≤ 0.36788 * w := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    rw [hLw]; linarith
  have hL0 : 0 < Real.log (m ^ 3) := Real.log_pos (by linarith)
  set L := Real.log (m ^ 3)
  set Λ := 17.659 * w with hΛ
  have hΛ0 : 0 < Λ := by positivity
  have hpi := Real.pi_pos
  have hlhs : 2 * (1 / (8 * π) * (√(m ^ 3) * L)) * (m + 3)
      ≤ 2 * (1 / (8 * π) * (√(m ^ 3) * Λ)) * (m + 3) := by
    have : √(m ^ 3) * L ≤ √(m ^ 3) * Λ := mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg _)
    have h8 : 0 ≤ 1 / (8 * π) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h8]
  have hrhs : (m ^ 3 - 2) / Λ ^ 2 ≤ (m ^ 3 - 2) / L ^ 2 :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) (pow_le_pow_left₀ hL0.le hL 2)
  have hP := tail3_poly hw2 h16
  rw [hwm, ← hx, ← hΛ] at hP
  have hmain : 2 * (1 / (8 * π) * (√(m ^ 3) * Λ)) * (m + 3)
      < 3 * ((m ^ 3 - 2) / Λ ^ 2 - 2.886) := by
    rw [hsx, ← hwm]
    rw [← hwm] at hP
    have hΛ2 : 0 < Λ ^ 2 := by positivity
    have e1 : 2 * (1 / (8 * π) * (w ^ 24 * Λ)) * (w ^ 16 + 3)
        = w ^ 24 * Λ ^ 3 * (w ^ 16 + 3) / (4 * π * Λ ^ 2) := by
      field_simp; ring
    have e2 : 3 * (((w ^ 16) ^ 3 - 2) / Λ ^ 2 - 2.886)
        = (12 * π * ((w ^ 16) ^ 3 - 2) - 34.632 * π * Λ ^ 2) / (4 * π * Λ ^ 2) := by
      field_simp; ring
    rw [e1, e2]
    apply div_lt_div_of_pos_right _ (by positivity)
    have e3 : (w ^ 16) ^ 3 = w ^ 48 := by ring
    rw [e3]
    rw [show (w ^ 16) ^ 3 = w ^ 48 by ring] at hP
    nlinarith [mul_pos hpi hΛ2]
  calc 2 * (1 / (8 * π) * (√(m ^ 3) * L)) * (m + 3) ≤ _ := hlhs
    _ < _ := hmain
    _ ≤ 3 * ((m ^ 3 - 2) / L ^ 2 - 2.886) := by linarith

/-- **`k = 3`, `n ≥ 10⁷`.** Schoenfeld's bound gives
`π((n+1)³)/(n+1)³ < π(n³)/n³` for every `n ≥ 10⁷`. -/
theorem tail_three (hS : ∀ x : ℝ, 2657 ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logIntegral x| < 1 / (8 * π) * (√x * Real.log x)) {n : ℕ} (hn : 10 ^ 7 ≤ n) :
    (Nat.primeCounting ((n + 1) ^ 3) : ℝ) / (((n : ℝ) + 1) ^ 3) <
      (Nat.primeCounting (n ^ 3) : ℝ) / ((n : ℝ) ^ 3) := by
  have hnR : (10 : ℝ) ^ 7 ≤ n := by exact_mod_cast hn
  set m : ℝ := (n : ℝ) with hmdef
  set x : ℝ := m ^ 3 with hxdef
  set y : ℝ := (m + 1) ^ 3 with hydef
  have hm0 : 0 < m := by linarith
  have hx0 : 0 < x := by positivity
  have hxy : x < y := by
    rw [hxdef, hydef]; exact pow_lt_pow_left₀ (by linarith) hm0.le (by norm_num)
  have hy0 : 0 < y := by linarith
  have hx2657 : (2657 : ℝ) ≤ x := by rw [hxdef]; nlinarith
  have hfx : ⌊x⌋₊ = n ^ 3 := by
    rw [hxdef, hmdef, show (n : ℝ) ^ 3 = ((n ^ 3 : ℕ) : ℝ) by push_cast; ring]
    exact Nat.floor_natCast _
  have hfy : ⌊y⌋₊ = (n + 1) ^ 3 := by
    rw [hydef, hmdef, show ((n : ℝ) + 1) ^ 3 = (((n + 1) ^ 3 : ℕ) : ℝ) by push_cast; ring]
    exact Nat.floor_natCast _
  have hSx := hS x hx2657
  have hSy := hS y (by linarith)
  rw [hfx] at hSx
  rw [hfy] at hSy
  have hlx : 2 ≤ Real.log x := by
    have h7 : Real.exp 2 ≤ x := by
      have : Real.exp 2 < 8 := by
        have := Real.exp_one_lt_d9
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith [Real.exp_pos 1]
      linarith
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) h7
  set Ex := 1 / (8 * π) * (√x * Real.log x)
  set Ey := 1 / (8 * π) * (√y * Real.log y)
  set Dl := (x - 2) / Real.log x ^ 2 - 2.886
  have hpi := Real.pi_pos
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx0
  have hsy : 0 < √y := Real.sqrt_pos.mpr hy0
  have hEx : Ex / x = 1 / (8 * π) * (Real.log x / √x) := by
    have h : √x * Real.log x / x = Real.log x / √x := by
      rw [div_eq_div_iff hx0.ne' hsx.ne']
      have := Real.mul_self_sqrt hx0.le
      linear_combination Real.log x * this
    simp only [Ex]; rw [mul_div_assoc, h]
  have hEy : Ey / y = 1 / (8 * π) * (Real.log y / √y) := by
    have h : √y * Real.log y / y = Real.log y / √y := by
      rw [div_eq_div_iff hy0.ne' hsy.ne']
      have := Real.mul_self_sqrt hy0.le
      linear_combination Real.log y * this
    simp only [Ey]; rw [mul_div_assoc, h]
  have hmono : Ey / y ≤ Ex / x := by
    rw [hEx, hEy]
    exact mul_le_mul_of_nonneg_left (log_div_sqrt_anti hx0 hlx hxy.le) (by positivity)
  have hratio : 3 / (m + 3) ≤ 1 - x / y := by
    have h1 := one_sub_ratio_ge n 3 (by omega)
    push_cast at h1
    exact h1
  have hcore := tail3_core hnR
  have hDl : 0 < Dl := by
    have : 0 < 2 * Ex * (m + 3) := by positivity
    simp only [Dl]; nlinarith
  have hkey : Ex / x + Ey / y < (1 - x / y) * Dl / x := by
    have h1 : 2 * Ex * (m + 3) < 3 * Dl := hcore
    have h2 : 2 * (Ex / x) < 3 / (m + 3) * Dl / x := by
      rw [div_mul_eq_mul_div, div_div, lt_div_iff₀ (by positivity)]
      have e : 2 * (Ex / x) * ((m + 3) * x) = 2 * Ex * (m + 3) := by field_simp
      rw [e]; linarith
    have h3 : 3 / (m + 3) * Dl / x ≤ (1 - x / y) * Dl / x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hratio hDl.le) hx0.le
    linarith
  exact ratio_lt_of_bounds (by linarith) hxy hSx.le hSy.le (logIntegral_sub_ge (by linarith)) hkey


theorem main : H1 → H2 → H3 → H4 → type_of% @OeisA38098.conjecture1 := by
  intro h1 h2 h3 h4 k hk n hn
  have hS := h2 h1
  rcases lt_or_ge (n ^ k) (10 ^ 10) with hsmall | hbig
  · exact h3 k hk n hn hsmall
  rw [← Rat.cast_lt (K := ℝ)]
  push_cast
  rcases Nat.lt_or_ge k 4 with hk4 | hk4
  · obtain rfl : k = 3 := by omega
    rcases Nat.lt_or_ge n (10 ^ 7) with hn7 | hn7
    · have := h4 n hbig hn7
      rw [← Rat.cast_lt (K := ℝ)] at this
      push_cast at this
      exact this
    · exact tail_three hS hn7
  · have := tail hS hk4 hn hbig
    push_cast at this
    exact this

end OMA.R_OeisA38098_conjecture1_R1
