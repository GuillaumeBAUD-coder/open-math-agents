import OMAReductions.R_Erdos1038_erdos_1038_parts_ii_R1_H2_R1
import Mathlib

/-! Tao's interval-density trial from Shouqiao Wang's proof of Erdős 1038.
Port of plby/lean-proofs @8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
from ShouqiaoW/erdos @dc20752268ede5a3548e3d63ae74e45c3cfcf78c.
The bridge applies the source measure directly on the pinned support and root interval.

MIT License

Copyright (c) 2026 Shouqiao Wang

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
-- Credit: @marcusbuffett

section
open scoped ENNReal Real

open MeasureTheory Set Polynomial

namespace WangTrial

noncomputable section

def H (q : ℝ) : ℝ := 2 * q / (1 + q) ^ 2

def s (q : ℝ) : ℝ := (1 - q) / (1 + q)

def A (q : ℝ) : ℝ := Real.log (H q) / Real.log q

end

end WangTrial

end

section
open Set

namespace WangTrial

noncomputable section

theorem sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := by
  norm_num

end

end WangTrial

end

section
open Set

namespace WangTrial

noncomputable section

def taoUpperEdge : ℝ := 2 * Real.sqrt 2

lemma seven_fifths_lt_sqrt_two : (7 / 5 : ℝ) < Real.sqrt 2 := by
  have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [sqrt_two_sq]

end

end WangTrial

end

section
open Set

open scoped Interval

namespace WangTrial

noncomputable section

def taoLogPrimitive (x : ℝ) : ℝ :=
  x - x * Real.log |x|

theorem taoLogPrimitive_zero : taoLogPrimitive 0 = 0 := by
  simp [taoLogPrimitive]

theorem continuous_taoLogPrimitive : Continuous taoLogPrimitive := by
  have hmul : Continuous (fun x : ℝ ↦ x * Real.log x) :=
    Real.continuous_mul_log
  change Continuous (fun x : ℝ ↦ x - x * Real.log |x|)
  simpa only [Real.log_abs] using! continuous_id.sub hmul

theorem hasDerivAt_taoLogPrimitive {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt taoLogPrimitive (-Real.log |x|) x := by
  have hmul : HasDerivAt (fun y : ℝ ↦ y * Real.log y)
      (Real.log x + 1) x := Real.hasDerivAt_mul_log hx
  have hderiv := (hasDerivAt_id x).sub hmul
  have hderiv' : HasDerivAt (fun y : ℝ ↦ y - y * Real.log y)
      (-Real.log x) x := by
    convert! hderiv using 1
    ring
  unfold taoLogPrimitive
  simpa only [Real.log_abs] using! hderiv'

theorem intervalIntegral_neg_log_abs (a b : ℝ) :
    (∫ x in a..b, -Real.log |x|) =
      taoLogPrimitive b - taoLogPrimitive a := by
  rw [intervalIntegral.integral_neg]
  rw [show (fun x : ℝ ↦ Real.log |x|) = Real.log by
    funext x
    exact Real.log_abs x]
  rw [integral_log]
  simp only [taoLogPrimitive, Real.log_abs]
  ring

theorem intervalDensityPotential_eq_primitive (a b t : ℝ) :
    (∫ s in a..b, -Real.log |t - s|) =
      taoLogPrimitive (b - t) - taoLogPrimitive (a - t) := by
  calc
    (∫ s in a..b, -Real.log |t - s|) =
        ∫ s in a..b, -Real.log |s - t| := by
      apply intervalIntegral.integral_congr
      intro s _
      change -Real.log |t - s| = -Real.log |s - t|
      rw [abs_sub_comm]
    _ = ∫ x in a - t..b - t, -Real.log |x| := by
      simpa only using!
        (intervalIntegral.integral_comp_sub_right
          (fun x : ℝ ↦ -Real.log |x|) t (a := a) (b := b))
    _ = taoLogPrimitive (b - t) - taoLogPrimitive (a - t) :=
      intervalIntegral_neg_log_abs (a - t) (b - t)

def taoCaseThreeInputFloor : ℝ := 953 / 1250

def taoCaseThreeInputCeiling : ℝ := 27987 / 10000

def taoCaseThreeCenterFloor : ℝ := 2203 / 1250

def taoCaseThreeCenterCeiling : ℝ := 17987 / 10000

def taoCaseThreeA : ℝ := 192829 / 1000000

def taoCaseThreeB : ℝ := 28 / 125

def taoCaseThreeC : ℝ := 31 / 200

def taoCaseThreeLeftA : ℝ := 163 / 100

def taoCaseThreeLeftB : ℝ := 1919 / 1000

def taoCaseThreePotential (t : ℝ) : ℝ :=
  -Real.log t +
    taoCaseThreeA *
      (taoLogPrimitive (taoUpperEdge - t) -
        taoLogPrimitive (taoCaseThreeLeftA - t)) +
    taoCaseThreeB *
      (taoLogPrimitive (taoUpperEdge - t) -
        taoLogPrimitive (taoCaseThreeLeftB - t)) -
    taoCaseThreeC * Real.log |taoUpperEdge - t|

theorem tao_case_three_center_interval_mem_input
    {t0 t : ℝ}
    (ht0Lower : taoCaseThreeCenterFloor ≤ t0)
    (ht0Upper : t0 ≤ taoCaseThreeCenterCeiling)
    (ht : t ∈ Icc (t0 - 1) (t0 + 1)) :
    t ∈ Icc taoCaseThreeInputFloor taoCaseThreeInputCeiling := by
  unfold taoCaseThreeCenterFloor taoCaseThreeCenterCeiling
    taoCaseThreeInputFloor taoCaseThreeInputCeiling at *
  constructor <;> linarith [ht.1, ht.2]

end

end WangTrial

end

section
open Set

namespace WangTrial

noncomputable section

def taoCaseThreePotentialDerivative (t : ℝ) : ℝ :=
  -1 / t + taoCaseThreeA *
      (Real.log |taoUpperEdge - t| -
        Real.log |taoCaseThreeLeftA - t|) +
    taoCaseThreeB *
      (Real.log |taoUpperEdge - t| -
        Real.log |taoCaseThreeLeftB - t|) +
    taoCaseThreeC / (taoUpperEdge - t)

theorem hasDerivAt_taoLogPrimitive_const_sub
    {c t : ℝ} (hct : c - t ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ taoLogPrimitive (c - x))
      (Real.log |c - t|) t := by
  have hinner : HasDerivAt (fun x : ℝ ↦ c - x) (-1) t := by
    convert! (hasDerivAt_const t c).sub (hasDerivAt_id t) using 1
    ring
  have hcomp := (hasDerivAt_taoLogPrimitive hct).comp t hinner
  convert! hcomp using 1
  ring

theorem hasDerivAt_log_abs_const_sub
    {c t : ℝ} (hct : c - t ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ Real.log |c - x|)
      (-1 / (c - t)) t := by
  have hinner : HasDerivAt (fun x : ℝ ↦ c - x) (-1) t := by
    convert! (hasDerivAt_const t c).sub (hasDerivAt_id t) using 1
    ring
  have hcomp := (Real.hasDerivAt_log hct).comp t hinner
  rw [show (fun x : ℝ ↦ Real.log |c - x|) =
      fun x : ℝ ↦ Real.log (c - x) by
    funext x
    exact Real.log_abs (c - x)]
  convert! hcomp using 1
  ring

theorem hasDerivAt_taoCaseThreePotential {t : ℝ}
    (ht : t ≠ 0)
    (hM : taoUpperEdge - t ≠ 0)
    (ha : taoCaseThreeLeftA - t ≠ 0)
    (hb : taoCaseThreeLeftB - t ≠ 0) :
    HasDerivAt taoCaseThreePotential
      (taoCaseThreePotentialDerivative t) t := by
  have hzero : HasDerivAt (fun x : ℝ ↦ -Real.log x) (-1 / t) t := by
    convert! (Real.hasDerivAt_log ht).neg using 1
    ring
  have hA := ((hasDerivAt_taoLogPrimitive_const_sub hM).sub
    (hasDerivAt_taoLogPrimitive_const_sub ha)).const_mul taoCaseThreeA
  have hB := ((hasDerivAt_taoLogPrimitive_const_sub hM).sub
    (hasDerivAt_taoLogPrimitive_const_sub hb)).const_mul taoCaseThreeB
  have hC := (hasDerivAt_log_abs_const_sub hM).const_mul (-taoCaseThreeC)
  convert! ((hzero.add hA).add hB).add hC using 1
  · funext x
    unfold taoCaseThreePotential
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · unfold taoCaseThreePotentialDerivative
    ring

theorem tao_case_three_inputCeiling_lt_upperEdge :
    taoCaseThreeInputCeiling < taoUpperEdge := by
  unfold taoCaseThreeInputCeiling taoUpperEdge
  nlinarith [seven_fifths_lt_sqrt_two]

theorem continuousOn_taoCaseThreePotential_input :
    ContinuousOn taoCaseThreePotential
      (Icc taoCaseThreeInputFloor taoCaseThreeInputCeiling) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have htPos : 0 < t := by
    unfold taoCaseThreeInputFloor at ht
    norm_num at ht ⊢
    linarith
  have hMPos : 0 < taoUpperEdge - t :=
    sub_pos.mpr (ht.2.trans_lt tao_case_three_inputCeiling_lt_upperEdge)
  have hzero : ContinuousAt (fun x : ℝ ↦ -Real.log x) t :=
    (Real.continuousAt_log htPos.ne').neg
  have hprimM : ContinuousAt
      (fun x : ℝ ↦ taoLogPrimitive (taoUpperEdge - x)) t :=
    continuous_taoLogPrimitive.continuousAt.comp
      (continuousAt_const.sub continuousAt_id)
  have hprimA : ContinuousAt
      (fun x : ℝ ↦ taoLogPrimitive (taoCaseThreeLeftA - x)) t :=
    continuous_taoLogPrimitive.continuousAt.comp
      (continuousAt_const.sub continuousAt_id)
  have hprimB : ContinuousAt
      (fun x : ℝ ↦ taoLogPrimitive (taoCaseThreeLeftB - x)) t :=
    continuous_taoLogPrimitive.continuousAt.comp
      (continuousAt_const.sub continuousAt_id)
  have hlogM : ContinuousAt
      (fun x : ℝ ↦ Real.log |taoUpperEdge - x|) t := by
    simpa only [Real.log_abs] using!
      (Real.continuousAt_log hMPos.ne').comp
        (continuousAt_const.sub continuousAt_id)
  exact (((hzero.add ((hprimM.sub hprimA).const_mul taoCaseThreeA)).add
    ((hprimM.sub hprimB).const_mul taoCaseThreeB)).sub
      (hlogM.const_mul taoCaseThreeC))

end

end WangTrial

end

section
open Finset

namespace WangTrial

noncomputable section

def atanhLowerRat : Nat → Rat → Rat
  | 0, _ => 0
  | n + 1, t =>
      atanhLowerRat n t + 2 * t ^ (2 * n + 1) / (2 * n + 1)

def atanhUpperRat (n : Nat) (t : Rat) : Rat :=
  atanhLowerRat n t + 2 * t ^ (2 * n + 1) / (1 - t ^ 2)

def atanhLowerReal (n : Nat) (t : ℝ) : ℝ :=
  2 * (∑ i ∈ Finset.range n,
    t ^ (2 * i + 1) / (2 * (i : ℝ) + 1))

def atanhUpperReal (n : Nat) (t : ℝ) : ℝ :=
  atanhLowerReal n t + 2 * t ^ (2 * n + 1) / (1 - t ^ 2)

theorem atanhLowerRat_cast (n : Nat) (t : Rat) :
    ((atanhLowerRat n t : Rat) : ℝ) = atanhLowerReal n (t : ℝ) := by
  induction n with
  | zero =>
      simp [atanhLowerRat, atanhLowerReal]
  | succ n ih =>
      rw [atanhLowerRat]
      simp only [Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat,
        Rat.cast_pow]
      rw [ih]
      simp [atanhLowerReal, Finset.sum_range_succ]
      ring

theorem atanhUpperRat_cast (n : Nat) (t : Rat) :
    ((atanhUpperRat n t : Rat) : ℝ) = atanhUpperReal n (t : ℝ) := by
  simp [atanhUpperRat, atanhUpperReal, atanhLowerRat_cast]

theorem log_lower_bound_of_rat (r t : Rat) (n : Nat)
    (ht0 : 0 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (hr : (r : ℝ) = (1 + (t : ℝ)) / (1 - (t : ℝ))) :
    ((atanhLowerRat n t : Rat) : ℝ) ≤ Real.log (r : ℝ) := by
  have h := Real.sum_range_le_log_div ht0 ht1 n
  rw [atanhLowerRat_cast]
  unfold atanhLowerReal
  rw [hr]
  nlinarith

theorem log_upper_bound_of_rat (r t : Rat) (n : Nat)
    (ht0 : 0 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (hr : (r : ℝ) = (1 + (t : ℝ)) / (1 - (t : ℝ))) :
    Real.log (r : ℝ) ≤ ((atanhUpperRat n t : Rat) : ℝ) := by
  have h := Real.log_div_le_sum_range_add ht0 ht1 n
  rw [atanhUpperRat_cast]
  unfold atanhUpperReal atanhLowerReal
  rw [hr]
  have h2 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  calc
    Real.log ((1 + (t : ℝ)) / (1 - (t : ℝ))) =
        2 * (1 / 2 * Real.log
          ((1 + (t : ℝ)) / (1 - (t : ℝ)))) := by ring
    _ ≤ 2 * (∑ i ∈ Finset.range n,
          (t : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1) +
          (t : ℝ) ^ (2 * n + 1) / (1 - (t : ℝ) ^ 2)) := h2
    _ = 2 * ∑ i ∈ Finset.range n,
          (t : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1) +
          2 * (t : ℝ) ^ (2 * n + 1) / (1 - (t : ℝ) ^ 2) := by ring

end

end WangTrial

end

section
namespace WangTrial

noncomputable section

def logAtanhParameterRat (r : Rat) : Rat := (r - 1) / (r + 1)

def logLowerRat (n : Nat) (r : Rat) : Rat :=
  if 1 ≤ r then
    atanhLowerRat n (logAtanhParameterRat r)
  else
    -atanhUpperRat n (logAtanhParameterRat (1 / r))

def logUpperRat (n : Nat) (r : Rat) : Rat :=
  if 1 ≤ r then
    atanhUpperRat n (logAtanhParameterRat r)
  else
    -atanhLowerRat n (logAtanhParameterRat (1 / r))

private theorem atanhParameter_nonneg_lt_one_of_one_le
    {r : Rat} (hr : (1 : Rat) ≤ r) :
    (0 : ℝ) ≤ (logAtanhParameterRat r : Rat) ∧
      ((logAtanhParameterRat r : Rat) : ℝ) < 1 := by
  have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hden : (0 : ℝ) < (r : ℝ) + 1 := by linarith
  constructor
  · rw [logAtanhParameterRat]
    norm_num only [Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one]
    exact div_nonneg (by linarith) hden.le
  · rw [logAtanhParameterRat]
    norm_num only [Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one]
    rw [div_lt_one hden]
    linarith

private theorem atanhParameter_ratio_of_one_le
    {r : Rat} (hr : (1 : Rat) ≤ r) :
    (r : ℝ) =
      (1 + ((logAtanhParameterRat r : Rat) : ℝ)) /
        (1 - ((logAtanhParameterRat r : Rat) : ℝ)) := by
  have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hden : (r : ℝ) + 1 ≠ 0 := by linarith
  rw [logAtanhParameterRat]
  norm_num only [Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one]
  field_simp [hden]
  ring

theorem logLowerRat_le_log {n : Nat} {r : Rat} (hr : (0 : Rat) < r) :
    ((logLowerRat n r : Rat) : ℝ) ≤ Real.log (r : ℝ) := by
  by_cases h1 : (1 : Rat) ≤ r
  · rw [logLowerRat, if_pos h1]
    exact log_lower_bound_of_rat r (logAtanhParameterRat r) n
      (atanhParameter_nonneg_lt_one_of_one_le h1).1
      (atanhParameter_nonneg_lt_one_of_one_le h1).2
      (atanhParameter_ratio_of_one_le h1)
  · rw [logLowerRat, if_neg h1]
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    have hinv : (1 : Rat) ≤ 1 / r := by
      rw [le_div_iff₀ hr]
      simpa using! (le_of_not_ge h1)
    have hupper := log_upper_bound_of_rat (1 / r)
      (logAtanhParameterRat (1 / r)) n
      (atanhParameter_nonneg_lt_one_of_one_le hinv).1
      (atanhParameter_nonneg_lt_one_of_one_le hinv).2
      (atanhParameter_ratio_of_one_le hinv)
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one] at hupper ⊢
    have hlog : Real.log (1 / (r : ℝ)) = -Real.log (r : ℝ) := by
      rw [one_div, Real.log_inv]
    rw [hlog] at hupper
    linarith

theorem log_le_logUpperRat {n : Nat} {r : Rat} (hr : (0 : Rat) < r) :
    Real.log (r : ℝ) ≤ ((logUpperRat n r : Rat) : ℝ) := by
  by_cases h1 : (1 : Rat) ≤ r
  · rw [logUpperRat, if_pos h1]
    exact log_upper_bound_of_rat r (logAtanhParameterRat r) n
      (atanhParameter_nonneg_lt_one_of_one_le h1).1
      (atanhParameter_nonneg_lt_one_of_one_le h1).2
      (atanhParameter_ratio_of_one_le h1)
  · rw [logUpperRat, if_neg h1]
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    have hinv : (1 : Rat) ≤ 1 / r := by
      rw [le_div_iff₀ hr]
      simpa using! (le_of_not_ge h1)
    have hlower := log_lower_bound_of_rat (1 / r)
      (logAtanhParameterRat (1 / r)) n
      (atanhParameter_nonneg_lt_one_of_one_le hinv).1
      (atanhParameter_nonneg_lt_one_of_one_le hinv).2
      (atanhParameter_ratio_of_one_le hinv)
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one] at hlower ⊢
    have hlog : Real.log (1 / (r : ℝ)) = -Real.log (r : ℝ) := by
      rw [one_div, Real.log_inv]
    rw [hlog] at hlower
    linarith

def sqrtBoundsRat : Nat → Rat → Rat × Rat
  | 0, r => (0, max 1 r)
  | n + 1, r =>
      let B := sqrtBoundsRat n r
      let m := (B.1 + B.2) / 2
      if m * m ≤ r then (m, B.2) else (B.1, m)

def sqrtLowerRat (n : Nat) (r : Rat) : Rat := (sqrtBoundsRat n r).1

def sqrtUpperRat (n : Nat) (r : Rat) : Rat := (sqrtBoundsRat n r).2

theorem sqrtBoundsRat_invariant (n : Nat) {r : Rat} (hr : 0 ≤ r) :
    0 ≤ (sqrtBoundsRat n r).1 ∧
      (sqrtBoundsRat n r).1 ≤ (sqrtBoundsRat n r).2 ∧
      (sqrtBoundsRat n r).1 * (sqrtBoundsRat n r).1 ≤ r ∧
      r ≤ (sqrtBoundsRat n r).2 * (sqrtBoundsRat n r).2 := by
  induction n with
  | zero =>
      simp only [sqrtBoundsRat, zero_mul]
      constructor
      · exact le_rfl
      constructor
      · exact (show (0 : Rat) ≤ 1 by norm_num).trans (le_max_left 1 r)
      constructor
      · exact hr
      · by_cases hr1 : r ≤ 1
        · rw [max_eq_left hr1]
          norm_num
          exact hr1
        · have h1r : 1 ≤ r := le_of_not_ge hr1
          rw [max_eq_right h1r]
          nlinarith
  | succ n ih =>
      let B := sqrtBoundsRat n r
      let m := (B.1 + B.2) / 2
      have hB : 0 ≤ B.1 ∧ B.1 ≤ B.2 ∧ B.1 * B.1 ≤ r ∧
          r ≤ B.2 * B.2 := by
        simpa only [B] using! ih
      have hm0 : 0 ≤ m := by
        dsimp only [m]
        nlinarith [hB.1, hB.2.1]
      have hlm : B.1 ≤ m := by
        dsimp only [m]
        nlinarith [hB.2.1]
      have hmh : m ≤ B.2 := by
        dsimp only [m]
        nlinarith [hB.2.1]
      by_cases hsq : m * m ≤ r
      · change 0 ≤ (if m * m ≤ r then (m, B.2) else (B.1, m)).1 ∧
          (if m * m ≤ r then (m, B.2) else (B.1, m)).1 ≤
            (if m * m ≤ r then (m, B.2) else (B.1, m)).2 ∧
          (if m * m ≤ r then (m, B.2) else (B.1, m)).1 *
              (if m * m ≤ r then (m, B.2) else (B.1, m)).1 ≤ r ∧
          r ≤ (if m * m ≤ r then (m, B.2) else (B.1, m)).2 *
            (if m * m ≤ r then (m, B.2) else (B.1, m)).2
        rw [if_pos hsq]
        exact ⟨hm0, hmh, hsq, hB.2.2.2⟩
      · change 0 ≤ (if m * m ≤ r then (m, B.2) else (B.1, m)).1 ∧
          (if m * m ≤ r then (m, B.2) else (B.1, m)).1 ≤
            (if m * m ≤ r then (m, B.2) else (B.1, m)).2 ∧
          (if m * m ≤ r then (m, B.2) else (B.1, m)).1 *
              (if m * m ≤ r then (m, B.2) else (B.1, m)).1 ≤ r ∧
          r ≤ (if m * m ≤ r then (m, B.2) else (B.1, m)).2 *
            (if m * m ≤ r then (m, B.2) else (B.1, m)).2
        rw [if_neg hsq]
        exact ⟨hB.1, hlm, hB.2.2.1, le_of_not_ge hsq⟩

theorem sqrtLowerRat_le_sqrt {n : Nat} {r : Rat} (hr : 0 ≤ r) :
    ((sqrtLowerRat n r : Rat) : ℝ) ≤ Real.sqrt (r : ℝ) := by
  have hB := sqrtBoundsRat_invariant n hr
  have hlo : (0 : ℝ) ≤ ((sqrtLowerRat n r : Rat) : ℝ) := by
    exact_mod_cast hB.1
  have hr' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  apply (Real.le_sqrt hlo hr').2
  have hsq : ((sqrtLowerRat n r : Rat) : ℝ) * ((sqrtLowerRat n r : Rat) : ℝ) ≤
      (r : ℝ) := by
    exact_mod_cast hB.2.2.1
  simpa only [pow_two] using! hsq

theorem sqrt_le_sqrtUpperRat {n : Nat} {r : Rat} (hr : 0 ≤ r) :
    Real.sqrt (r : ℝ) ≤ ((sqrtUpperRat n r : Rat) : ℝ) := by
  have hB := sqrtBoundsRat_invariant n hr
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact_mod_cast hB.1.trans hB.2.1
  · have hsq : (r : ℝ) ≤
        ((sqrtUpperRat n r : Rat) : ℝ) * ((sqrtUpperRat n r : Rat) : ℝ) := by
      exact_mod_cast hB.2.2.2
    simpa only [pow_two] using! hsq

structure RatInterval where
  lo : Rat
  hi : Rat
deriving DecidableEq, Repr

namespace RatInterval

def Contains (I : RatInterval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def point (r : Rat) : RatInterval := ⟨r, r⟩

def add (I J : RatInterval) : RatInterval :=
  ⟨I.lo + J.lo, I.hi + J.hi⟩

def neg (I : RatInterval) : RatInterval := ⟨-I.hi, -I.lo⟩

def sub (I J : RatInterval) : RatInterval := add I (neg J)

def mul (I J : RatInterval) : RatInterval :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi))
      (min (I.hi * J.lo) (I.hi * J.hi)),
    max (max (I.lo * J.lo) (I.lo * J.hi))
      (max (I.hi * J.lo) (I.hi * J.hi))⟩

def inv? (I : RatInterval) : Option RatInterval :=
  if 0 < I.lo ∨ I.hi < 0 then some ⟨1 / I.hi, 1 / I.lo⟩ else none

def div? (I J : RatInterval) : Option RatInterval := do
  let Jinv ← inv? J
  pure (mul I Jinv)

def log? (n : Nat) (I : RatInterval) : Option RatInterval :=
  if 0 < I.lo then some ⟨logLowerRat n I.lo, logUpperRat n I.hi⟩ else none

def sqrt? (n : Nat) (I : RatInterval) : Option RatInterval :=
  if 0 ≤ I.lo then some ⟨sqrtLowerRat n I.lo, sqrtUpperRat n I.hi⟩ else none

theorem point_contains (r : Rat) : (point r).Contains (r : ℝ) := ⟨le_rfl, le_rfl⟩

theorem add_contains {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (add I J).Contains (x + y) := by
  constructor <;> norm_num only [add, Rat.cast_add] <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem neg_contains {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    (neg I).Contains (-x) := by
  constructor <;> norm_num only [neg, Rat.cast_neg] <;> linarith [hx.1, hx.2]

theorem sub_contains {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (sub I J).Contains (x - y) := by
  simpa only [sub, sub_eq_add_neg] using! add_contains hx (neg_contains hy)

private theorem mul_minmax_bounds {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have hab : a ≤ b := hx.1.trans hx.2
  have hcd : c ≤ d := hy.1.trans hy.2
  rcases le_total 0 x with hx0 | hx0 <;>
    rcases le_total 0 y with hy0 | hy0
  · have hb0 : 0 ≤ b := hx0.trans hx.2
    have hd0 : 0 ≤ d := hy0.trans hy.2
    constructor
    · by_cases ha0 : 0 ≤ a
      · apply min_le_of_left_le
        apply min_le_of_left_le
        calc
          a * c ≤ a * y := mul_le_mul_of_nonneg_left hy.1 ha0
          _ ≤ x * y := mul_le_mul_of_nonneg_right hx.1 hy0
      · apply min_le_of_left_le
        apply min_le_of_right_le
        exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ha0) hd0).trans
          (mul_nonneg hx0 hy0)
    · apply le_max_of_le_right
      apply le_max_of_le_right
      exact mul_le_mul hx.2 hy.2 hy0 hb0
  · have hb0 : 0 ≤ b := hx0.trans hx.2
    have hc0 : c ≤ 0 := hy.1.trans hy0
    constructor
    · apply min_le_of_right_le
      apply min_le_of_left_le
      calc
        b * c ≤ b * y := mul_le_mul_of_nonneg_left hy.1 hb0
        _ ≤ x * y := mul_le_mul_of_nonpos_right hx.2 hy0
    · by_cases ha0 : 0 ≤ a
      · apply le_max_of_le_left
        apply le_max_of_le_right
        calc
          x * y ≤ a * y := mul_le_mul_of_nonpos_right hx.1 hy0
          _ ≤ a * d := mul_le_mul_of_nonneg_left hy.2 ha0
      · apply le_max_of_le_left
        apply le_max_of_le_left
        calc
          x * y ≤ a * y := mul_le_mul_of_nonpos_right hx.1 hy0
          _ ≤ a * c := mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge ha0)
  · have ha0 : a ≤ 0 := hx.1.trans hx0
    have hd0 : 0 ≤ d := hy0.trans hy.2
    constructor
    · apply min_le_of_left_le
      apply min_le_of_right_le
      calc
        a * d ≤ a * y := mul_le_mul_of_nonpos_left hy.2 ha0
        _ ≤ x * y := mul_le_mul_of_nonneg_right hx.1 hy0
    · by_cases hb0 : 0 ≤ b
      · apply le_max_of_le_right
        apply le_max_of_le_right
        exact (mul_nonpos_of_nonpos_of_nonneg hx0 hy0).trans
          (mul_nonneg hb0 hd0)
      · apply le_max_of_le_right
        apply le_max_of_le_left
        calc
          x * y ≤ b * y := mul_le_mul_of_nonneg_right hx.2 hy0
          _ ≤ b * c := mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hb0)
  · have ha0 : a ≤ 0 := hx.1.trans hx0
    have hc0 : c ≤ 0 := hy.1.trans hy0
    constructor
    · by_cases hb0 : 0 ≤ b
      · apply min_le_of_right_le
        apply min_le_of_left_le
        exact (mul_nonpos_of_nonneg_of_nonpos hb0 hc0).trans (mul_nonneg_of_nonpos_of_nonpos hx0 hy0)
      · by_cases hd0 : 0 ≤ d
        · apply min_le_of_left_le
          apply min_le_of_right_le
          exact (mul_nonpos_of_nonpos_of_nonneg ha0 hd0).trans
            (mul_nonneg_of_nonpos_of_nonpos hx0 hy0)
        · apply min_le_of_right_le
          apply min_le_of_right_le
          calc
            b * d ≤ x * d := mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hd0)
            _ ≤ x * y := mul_le_mul_of_nonpos_left hy.2 hx0
    · apply le_max_of_le_left
      apply le_max_of_le_left
      calc
        x * y ≤ a * y := mul_le_mul_of_nonpos_right hx.1 hy0
        _ ≤ a * c := mul_le_mul_of_nonpos_left hy.1 ha0

theorem mul_contains {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (mul I J).Contains (x * y) := by
  simpa only [mul, Contains, Rat.cast_min, Rat.cast_max, Rat.cast_mul] using!
    mul_minmax_bounds hx hy

theorem inv_contains {I J : RatInterval} {x : ℝ} (hx : I.Contains x)
    (h : inv? I = some J) : J.Contains x⁻¹ := by
  by_cases hsign : 0 < I.lo ∨ I.hi < 0
  · rw [inv?, if_pos hsign] at h
    cases h
    simp only [Contains]
    norm_num
    rcases hsign with hlo | hhi
    · have hlo' : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hlo
      have hx' : 0 < x := hlo'.trans_le hx.1
      constructor
      · simpa only [one_div] using! one_div_le_one_div_of_le hx' hx.2
      · simpa only [one_div] using! one_div_le_one_div_of_le hlo' hx.1
    · have hhi' : (I.hi : ℝ) < 0 := by exact_mod_cast hhi
      have hx' : x < 0 := hx.2.trans_lt hhi'
      constructor
      · simpa only [one_div] using! one_div_le_one_div_of_neg_of_le hhi' hx.2
      · simpa only [one_div] using! one_div_le_one_div_of_neg_of_le hx' hx.1
  · simp only [inv?, if_neg hsign, reduceCtorEq] at h

theorem log_contains {n : Nat} {I J : RatInterval} {x : ℝ}
    (hx : I.Contains x) (h : log? n I = some J) : J.Contains (Real.log x) := by
  by_cases hlo : 0 < I.lo
  · rw [log?, if_pos hlo] at h
    cases h
    change ((logLowerRat n I.lo : Rat) : ℝ) ≤ Real.log x ∧
      Real.log x ≤ ((logUpperRat n I.hi : Rat) : ℝ)
    have hlo' : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hlo
    have hx' : 0 < x := hlo'.trans_le hx.1
    have hhi : (0 : Rat) < I.hi := by
      have hhi' : (0 : ℝ) < (I.hi : ℝ) := hx'.trans_le hx.2
      exact_mod_cast hhi'
    constructor
    · exact (logLowerRat_le_log (n := n) hlo).trans (Real.log_le_log hlo' hx.1)
    · exact (Real.log_le_log hx' hx.2).trans (log_le_logUpperRat (n := n) hhi)
  · simp only [log?, if_neg hlo, reduceCtorEq] at h

theorem sqrt_contains {n : Nat} {I J : RatInterval} {x : ℝ}
    (hx : I.Contains x) (h : sqrt? n I = some J) : J.Contains (Real.sqrt x) := by
  by_cases hlo : 0 ≤ I.lo
  · rw [sqrt?, if_pos hlo] at h
    cases h
    change ((sqrtLowerRat n I.lo : Rat) : ℝ) ≤ Real.sqrt x ∧
      Real.sqrt x ≤ ((sqrtUpperRat n I.hi : Rat) : ℝ)
    have hlo' : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hlo
    have hx0 : 0 ≤ x := hlo'.trans hx.1
    have hhi : (0 : Rat) ≤ I.hi := by
      have hhi' : (0 : ℝ) ≤ (I.hi : ℝ) := hx0.trans hx.2
      exact_mod_cast hhi'
    constructor
    · exact (sqrtLowerRat_le_sqrt (n := n) hlo).trans (Real.sqrt_le_sqrt hx.1)
    · exact (Real.sqrt_le_sqrt hx.2).trans (sqrt_le_sqrtUpperRat (n := n) hhi)
  · simp only [sqrt?, if_neg hlo, reduceCtorEq] at h

end RatInterval

end

end WangTrial

end

section
open Set

namespace WangTrial

noncomputable section

def taoCaseThreePotentialSecondDerivative (t : ℝ) : ℝ :=
  1 / t ^ 2 +
    taoCaseThreeA *
      (-1 / (taoUpperEdge - t) +
        1 / (taoCaseThreeLeftA - t)) +
    taoCaseThreeB *
      (-1 / (taoUpperEdge - t) +
        1 / (taoCaseThreeLeftB - t)) +
    taoCaseThreeC / (taoUpperEdge - t) ^ 2

theorem hasDerivAt_taoCaseThreePotentialDerivative {t : ℝ}
    (ht : t ≠ 0) (hM : taoUpperEdge - t ≠ 0)
    (ha : taoCaseThreeLeftA - t ≠ 0)
    (hb : taoCaseThreeLeftB - t ≠ 0) :
    HasDerivAt taoCaseThreePotentialDerivative
      (taoCaseThreePotentialSecondDerivative t) t := by
  have hrecip : HasDerivAt (fun x : ℝ ↦ -1 / x) (1 / t ^ 2) t := by
    convert! (hasDerivAt_const t (-1 : ℝ)).div (hasDerivAt_id t) ht using 1
    simp only [id_eq]
    field_simp [ht]
    ring
  have hA := ((hasDerivAt_log_abs_const_sub hM).sub
    (hasDerivAt_log_abs_const_sub ha)).const_mul taoCaseThreeA
  have hB := ((hasDerivAt_log_abs_const_sub hM).sub
    (hasDerivAt_log_abs_const_sub hb)).const_mul taoCaseThreeB
  have hC : HasDerivAt
      (fun x : ℝ ↦ taoCaseThreeC / (taoUpperEdge - x))
      (taoCaseThreeC / (taoUpperEdge - t) ^ 2) t := by
    have hden : HasDerivAt (fun x : ℝ ↦ taoUpperEdge - x) (-1) t := by
      convert! (hasDerivAt_const t taoUpperEdge).sub (hasDerivAt_id t) using 1
      ring
    convert! (hasDerivAt_const t taoCaseThreeC).div hden hM using 1
    field_simp [hM]
    ring
  convert! (((hrecip.add hA).add hB).add hC) using 1
  unfold taoCaseThreePotentialSecondDerivative
  ring

theorem hasDerivAt_deriv_taoCaseThreePotential {t : ℝ}
    (ht : t ≠ 0) (hM : taoUpperEdge - t ≠ 0)
    (ha : taoCaseThreeLeftA - t ≠ 0)
    (hb : taoCaseThreeLeftB - t ≠ 0) :
    HasDerivAt (deriv taoCaseThreePotential)
      (taoCaseThreePotentialSecondDerivative t) t := by
  have htM : t ≠ taoUpperEdge := (sub_ne_zero.mp hM).symm
  have hta : t ≠ taoCaseThreeLeftA := (sub_ne_zero.mp ha).symm
  have htb : t ≠ taoCaseThreeLeftB := (sub_ne_zero.mp hb).symm
  have heq : Filter.EventuallyEq (nhds t)
      (deriv taoCaseThreePotential) taoCaseThreePotentialDerivative := by
    filter_upwards [eventually_ne_nhds ht, eventually_ne_nhds htM,
      eventually_ne_nhds hta, eventually_ne_nhds htb] with y hy0 hyM hya hyb
    exact (hasDerivAt_taoCaseThreePotential hy0
      (sub_ne_zero.mpr hyM.symm) (sub_ne_zero.mpr hya.symm)
      (sub_ne_zero.mpr hyb.symm)).deriv
  exact (hasDerivAt_taoCaseThreePotentialDerivative ht hM ha hb).congr_of_eventuallyEq
    heq

theorem deriv2_taoCaseThreePotential {t : ℝ}
    (ht : t ≠ 0) (hM : taoUpperEdge - t ≠ 0)
    (ha : taoCaseThreeLeftA - t ≠ 0)
    (hb : taoCaseThreeLeftB - t ≠ 0) :
    deriv^[2] taoCaseThreePotential t =
      taoCaseThreePotentialSecondDerivative t := by
  rw [show deriv^[2] taoCaseThreePotential t =
      deriv (deriv taoCaseThreePotential) t by rfl]
  exact (hasDerivAt_deriv_taoCaseThreePotential ht hM ha hb).deriv

theorem tao_case_three_inputFloor_pos :
    0 < taoCaseThreeInputFloor := by
  norm_num [taoCaseThreeInputFloor]

theorem tao_case_three_inputFloor_lt_leftA :
    taoCaseThreeInputFloor < taoCaseThreeLeftA := by
  norm_num [taoCaseThreeInputFloor, taoCaseThreeLeftA]

theorem tao_case_three_leftA_lt_leftB :
    taoCaseThreeLeftA < taoCaseThreeLeftB := by
  norm_num [taoCaseThreeLeftA, taoCaseThreeLeftB]

theorem tao_case_three_leftA_lt_upperEdge :
    taoCaseThreeLeftA < taoUpperEdge := by
  unfold taoCaseThreeLeftA taoUpperEdge
  nlinarith [seven_fifths_lt_sqrt_two]

theorem tao_case_three_leftB_lt_upperEdge :
    taoCaseThreeLeftB < taoUpperEdge := by
  unfold taoCaseThreeLeftB taoUpperEdge
  nlinarith [seven_fifths_lt_sqrt_two]

theorem tao_case_three_transitionHigh_lt_inputCeiling :
    (51 / 20 : ℝ) < taoCaseThreeInputCeiling := by
  norm_num [taoCaseThreeInputCeiling]

theorem taoCaseThreePotentialSecondDerivative_pos_of_left
    {t : ℝ} (ht : t ∈ Ioo taoCaseThreeInputFloor taoCaseThreeLeftA) :
    0 < taoCaseThreePotentialSecondDerivative t := by
  have htPos : 0 < t := tao_case_three_inputFloor_pos.trans ht.1
  have haPos : 0 < taoCaseThreeLeftA - t := sub_pos.mpr ht.2
  have hbPos : 0 < taoCaseThreeLeftB - t :=
    sub_pos.mpr (ht.2.trans tao_case_three_leftA_lt_leftB)
  have hMPos : 0 < taoUpperEdge - t :=
    sub_pos.mpr (ht.2.trans tao_case_three_leftA_lt_upperEdge)
  have hAinv : 0 < -1 / (taoUpperEdge - t) +
      1 / (taoCaseThreeLeftA - t) := by
    have hden : taoCaseThreeLeftA - t < taoUpperEdge - t := by
      linarith [tao_case_three_leftA_lt_upperEdge]
    have := one_div_lt_one_div_of_lt haPos hden
    rw [neg_div]
    linarith
  have hBinv : 0 < -1 / (taoUpperEdge - t) +
      1 / (taoCaseThreeLeftB - t) := by
    have hden : taoCaseThreeLeftB - t < taoUpperEdge - t := by
      linarith [tao_case_three_leftB_lt_upperEdge]
    have := one_div_lt_one_div_of_lt hbPos hden
    rw [neg_div]
    linarith
  have hfirst : 0 < 1 / t ^ 2 :=
    div_pos zero_lt_one (sq_pos_of_pos htPos)
  have hA : 0 < taoCaseThreeA *
      (-1 / (taoUpperEdge - t) +
        1 / (taoCaseThreeLeftA - t)) :=
    mul_pos (by norm_num [taoCaseThreeA]) hAinv
  have hB : 0 < taoCaseThreeB *
      (-1 / (taoUpperEdge - t) +
        1 / (taoCaseThreeLeftB - t)) :=
    mul_pos (by norm_num [taoCaseThreeB]) hBinv
  have hC : 0 < taoCaseThreeC / (taoUpperEdge - t) ^ 2 :=
    div_pos (by norm_num [taoCaseThreeC]) (sq_pos_of_pos hMPos)
  unfold taoCaseThreePotentialSecondDerivative
  linarith

theorem taoCaseThreePotential_convexOn_left :
    ConvexOn ℝ (Icc taoCaseThreeInputFloor taoCaseThreeLeftA)
      taoCaseThreePotential := by
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _)
  · exact continuousOn_taoCaseThreePotential_input.mono fun _ ht ↦
      ⟨ht.1, ht.2.trans (by
        norm_num [taoCaseThreeLeftA, taoCaseThreeInputCeiling])⟩
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_taoCaseThreePotential
      (tao_case_three_inputFloor_pos.trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans tao_case_three_leftA_lt_upperEdge)).ne'
      (sub_pos.mpr ht.2).ne'
      (sub_pos.mpr (ht.2.trans tao_case_three_leftA_lt_leftB)).ne'
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_deriv_taoCaseThreePotential
      (tao_case_three_inputFloor_pos.trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans tao_case_three_leftA_lt_upperEdge)).ne'
      (sub_pos.mpr ht.2).ne'
      (sub_pos.mpr (ht.2.trans tao_case_three_leftA_lt_leftB)).ne'
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [deriv2_taoCaseThreePotential
      (tao_case_three_inputFloor_pos.trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans tao_case_three_leftA_lt_upperEdge)).ne'
      (sub_pos.mpr ht.2).ne'
      (sub_pos.mpr (ht.2.trans tao_case_three_leftA_lt_leftB)).ne']
    exact (taoCaseThreePotentialSecondDerivative_pos_of_left ht).le

theorem taoCaseThreePotentialDerivative_pos_of_middle
    {t : ℝ} (ht : t ∈ Ioo taoCaseThreeLeftA taoCaseThreeLeftB) :
    0 < taoCaseThreePotentialDerivative t := by
  have haPos : 0 < taoCaseThreeLeftA := by
    norm_num [taoCaseThreeLeftA]
  have htPos : 0 < t := haPos.trans ht.1
  have hMPos : 0 < taoUpperEdge - t :=
    sub_pos.mpr (ht.2.trans tao_case_three_leftB_lt_upperEdge)
  have htaPos : 0 < t - taoCaseThreeLeftA := sub_pos.mpr ht.1
  have hbtPos : 0 < taoCaseThreeLeftB - t := sub_pos.mpr ht.2
  have hthreshold :
      4 * taoCaseThreeLeftB - 3 * taoCaseThreeLeftA < taoUpperEdge := by
    unfold taoCaseThreeLeftA taoCaseThreeLeftB taoUpperEdge
    nlinarith [seven_fifths_lt_sqrt_two]
  have hratioA : (3 : ℝ) <
      (taoUpperEdge - t) / (t - taoCaseThreeLeftA) := by
    rw [lt_div_iff₀ htaPos]
    nlinarith [ht.2, hthreshold]
  have hratioB : (4 : ℝ) <
      (taoUpperEdge - t) / (taoCaseThreeLeftB - t) := by
    rw [lt_div_iff₀ hbtPos]
    nlinarith [ht.1, hthreshold]
  have hlogThree : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_three
  have hlogFour : (4 / 3 : ℝ) < Real.log 4 := by
    have hbound := logLowerRat_le_log
      (n := 3) (r := (4 : Rat)) (by norm_num)
    have hrat : (4 / 3 : ℝ) <
        ((logLowerRat 3 4 : Rat) : ℝ) := by
      norm_num [logLowerRat, logAtanhParameterRat, atanhLowerRat]
    exact hrat.trans_le hbound
  have hlogA : (1 : ℝ) <
      Real.log |taoUpperEdge - t| -
        Real.log |taoCaseThreeLeftA - t| := by
    rw [abs_of_pos hMPos,
      abs_of_neg (sub_neg.mpr ht.1)]
    rw [show -(taoCaseThreeLeftA - t) =
      t - taoCaseThreeLeftA by ring]
    rw [← Real.log_div hMPos.ne' htaPos.ne']
    exact hlogThree.trans
      (Real.log_lt_log (by norm_num) hratioA)
  have hlogB : (4 / 3 : ℝ) <
      Real.log |taoUpperEdge - t| -
        Real.log |taoCaseThreeLeftB - t| := by
    rw [abs_of_pos hMPos, abs_of_pos hbtPos]
    rw [← Real.log_div hMPos.ne' hbtPos.ne']
    exact hlogFour.trans
      (Real.log_lt_log (by norm_num) hratioB)
  have hrecip :
      -1 / taoCaseThreeLeftA < -1 / t := by
    have hinv := one_div_lt_one_div_of_lt haPos ht.1
    simpa only [neg_div] using! neg_lt_neg hinv
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := by
    norm_num
  have hMUpper : taoUpperEdge < (283 / 100 : ℝ) := by
    unfold taoUpperEdge
    have hsqrtNonneg := Real.sqrt_nonneg 2
    nlinarith
  have hC : (1 / 8 : ℝ) <
      taoCaseThreeC / (taoUpperEdge - t) := by
    rw [lt_div_iff₀ hMPos]
    have htLower : (163 / 100 : ℝ) < t := by
      simpa only [taoCaseThreeLeftA] using! ht.1
    norm_num only [taoCaseThreeC]
    nlinarith [htLower, hMUpper]
  have hApos : 0 < taoCaseThreeA := by
    norm_num [taoCaseThreeA]
  have hBpos : 0 < taoCaseThreeB := by
    norm_num [taoCaseThreeB]
  have hscaledA := mul_lt_mul_of_pos_left hlogA hApos
  have hscaledB := mul_lt_mul_of_pos_left hlogB hBpos
  have hbase : 0 <
      -1 / taoCaseThreeLeftA + taoCaseThreeA * 1 +
        taoCaseThreeB * (4 / 3) + (1 / 8 : ℝ) := by
    norm_num [taoCaseThreeLeftA, taoCaseThreeA, taoCaseThreeB]
  unfold taoCaseThreePotentialDerivative
  nlinarith

theorem taoCaseThreePotential_strictMonoOn_middle :
    StrictMonoOn taoCaseThreePotential
      (Icc taoCaseThreeLeftA taoCaseThreeLeftB) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact continuousOn_taoCaseThreePotential_input.mono fun _ ht ↦ by
      constructor
      · exact (by
          norm_num [taoCaseThreeInputFloor, taoCaseThreeLeftA] at ht ⊢
          linarith [ht.1])
      · exact (by
          norm_num [taoCaseThreeInputCeiling, taoCaseThreeLeftB] at ht ⊢
          linarith [ht.2])
  · rw [interior_Icc]
    intro t ht
    rw [(hasDerivAt_taoCaseThreePotential
      (by
        have : 0 < taoCaseThreeLeftA := by
          norm_num [taoCaseThreeLeftA]
        exact (this.trans ht.1).ne')
      (sub_pos.mpr (ht.2.trans tao_case_three_leftB_lt_upperEdge)).ne'
      (sub_neg.mpr ht.1).ne
      (sub_pos.mpr ht.2).ne').deriv]
    exact taoCaseThreePotentialDerivative_pos_of_middle ht

private theorem taoCaseThreePotentialSecondDerivative_eq_right
    {t : ℝ} :
    taoCaseThreePotentialSecondDerivative t =
      1 / t ^ 2 -
        (taoCaseThreeA + taoCaseThreeB) / (taoUpperEdge - t) -
        taoCaseThreeA / (t - taoCaseThreeLeftA) -
        taoCaseThreeB / (t - taoCaseThreeLeftB) +
        taoCaseThreeC / (taoUpperEdge - t) ^ 2 := by
  rw [taoCaseThreePotentialSecondDerivative,
    show taoCaseThreeLeftA - t =
      -(t - taoCaseThreeLeftA) by ring,
    show taoCaseThreeLeftB - t =
      -(t - taoCaseThreeLeftB) by ring,
    one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div]
  ring

theorem taoCaseThreePotentialSecondDerivative_neg_of_right_low
    {t : ℝ} (htLower : taoCaseThreeLeftB < t)
    (htUpper : t ≤ (11 / 5 : ℝ)) :
    taoCaseThreePotentialSecondDerivative t < 0 := by
  have htPos : 0 < t := by
    have : 0 < taoCaseThreeLeftB := by
      norm_num [taoCaseThreeLeftB]
    exact this.trans htLower
  have htaPos : 0 < t - taoCaseThreeLeftA :=
    sub_pos.mpr (tao_case_three_leftA_lt_leftB.trans htLower)
  have htbPos : 0 < t - taoCaseThreeLeftB := sub_pos.mpr htLower
  have hMPos : 0 < taoUpperEdge - t := by
    have hM : (14 / 5 : ℝ) < taoUpperEdge := by
      unfold taoUpperEdge
      nlinarith [seven_fifths_lt_sqrt_two]
    linarith
  rw [taoCaseThreePotentialSecondDerivative_eq_right]
  have htBound : (19 / 10 : ℝ) < t := by
    norm_num [taoCaseThreeLeftB] at htLower ⊢
    linarith
  have htSq : (10 / 3 : ℝ) < t ^ 2 := by
    nlinarith
  have hfirst : 1 / t ^ 2 < (3 / 10 : ℝ) := by
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 10 / 3) htSq
    norm_num at h ⊢
    exact h
  have hu : (3 / 5 : ℝ) < taoUpperEdge - t := by
    have hM : (14 / 5 : ℝ) < taoUpperEdge := by
      unfold taoUpperEdge
      nlinarith [seven_fifths_lt_sqrt_two]
    linarith
  have huSq : (9 / 25 : ℝ) < (taoUpperEdge - t) ^ 2 := by
    nlinarith
  have hC : taoCaseThreeC / (taoUpperEdge - t) ^ 2 <
      (13 / 30 : ℝ) := by
    rw [div_lt_iff₀ (sq_pos_of_pos hMPos)]
    unfold taoCaseThreeC
    nlinarith
  have htaUpper : t - taoCaseThreeLeftA ≤ (57 / 100 : ℝ) := by
    unfold taoCaseThreeLeftA
    linarith
  have htbUpper : t - taoCaseThreeLeftB ≤ (281 / 1000 : ℝ) := by
    unfold taoCaseThreeLeftB
    linarith
  have hA : -taoCaseThreeA / (t - taoCaseThreeLeftA) ≤
      -taoCaseThreeA / (57 / 100 : ℝ) := by
    have hinv := one_div_le_one_div_of_le htaPos htaUpper
    have hmul := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ taoCaseThreeA by norm_num [taoCaseThreeA])
    convert! neg_le_neg hmul using 1 <;> ring
  have hB : -taoCaseThreeB / (t - taoCaseThreeLeftB) ≤
      -taoCaseThreeB / (281 / 1000 : ℝ) := by
    have hinv := one_div_le_one_div_of_le htbPos htbUpper
    have hmul := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ taoCaseThreeB by norm_num [taoCaseThreeB])
    convert! neg_le_neg hmul using 1 <;> ring
  have hshared :
      -(taoCaseThreeA + taoCaseThreeB) / (taoUpperEdge - t) < 0 := by
    exact div_neg_of_neg_of_pos (by
      norm_num [taoCaseThreeA, taoCaseThreeB]) hMPos
  have hbase :
      (3 / 10 : ℝ) + 13 / 30 -
        taoCaseThreeA / (57 / 100) -
        taoCaseThreeB / (281 / 1000) < 0 := by
    norm_num [taoCaseThreeA, taoCaseThreeB]
  ring_nf at hfirst hC hA hB hshared hbase ⊢
  linarith

theorem taoCaseThreePotentialSecondDerivative_neg_of_right_high
    {t : ℝ} (htLower : (11 / 5 : ℝ) ≤ t)
    (htUpper : t < (253 / 100 : ℝ)) :
    taoCaseThreePotentialSecondDerivative t < 0 := by
  have htPos : 0 < t := by linarith
  have htaPos : 0 < t - taoCaseThreeLeftA := by
    norm_num [taoCaseThreeLeftA] at htLower ⊢
    linarith
  have htbPos : 0 < t - taoCaseThreeLeftB := by
    norm_num [taoCaseThreeLeftB] at htLower ⊢
    linarith
  have hMPos : 0 < taoUpperEdge - t := by
    have hM : (14 / 5 : ℝ) < taoUpperEdge := by
      unfold taoUpperEdge
      nlinarith [seven_fifths_lt_sqrt_two]
    linarith
  rw [taoCaseThreePotentialSecondDerivative_eq_right]
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hsqrtNonneg := Real.sqrt_nonneg 2
  have hsqrtLower : (707 / 500 : ℝ) < Real.sqrt 2 := by
    nlinarith
  have hu : (149 / 500 : ℝ) < taoUpperEdge - t := by
    unfold taoUpperEdge
    linarith
  have huSq : (149 / 500 : ℝ) ^ 2 <
      (taoUpperEdge - t) ^ 2 := by
    nlinarith
  let K : ℝ := taoCaseThreeA + taoCaseThreeB
  have hKpos : 0 < K := by
    dsimp only [K]
    norm_num [taoCaseThreeA, taoCaseThreeB]
  have hquadBase : taoCaseThreeC <
      (7 / 20 : ℝ) * (149 / 500) ^ 2 +
        K * (149 / 500) := by
    dsimp only [K]
    norm_num [taoCaseThreeA, taoCaseThreeB, taoCaseThreeC]
  have hquad : taoCaseThreeC <
      (7 / 20 : ℝ) * (taoUpperEdge - t) ^ 2 +
        K * (taoUpperEdge - t) := by
    have hscaledSq := mul_lt_mul_of_pos_left huSq
      (by norm_num : (0 : ℝ) < 7 / 20)
    have hscaled := mul_lt_mul_of_pos_left hu hKpos
    linarith
  have hcombined :
      taoCaseThreeC / (taoUpperEdge - t) ^ 2 -
          K / (taoUpperEdge - t) < (7 / 20 : ℝ) := by
    rw [show taoCaseThreeC / (taoUpperEdge - t) ^ 2 -
        K / (taoUpperEdge - t) =
      (taoCaseThreeC - K * (taoUpperEdge - t)) /
        (taoUpperEdge - t) ^ 2 by
          field_simp [hMPos.ne']]
    rw [div_lt_iff₀ (sq_pos_of_pos hMPos)]
    linarith
  have htSq : (121 / 25 : ℝ) ≤ t ^ 2 := by
    nlinarith
  have hfirst : 1 / t ^ 2 ≤ (25 / 121 : ℝ) := by
    have h := one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 121 / 25) htSq
    norm_num at h ⊢
    exact h
  have htaUpper : t - taoCaseThreeLeftA < (9 / 10 : ℝ) := by
    unfold taoCaseThreeLeftA
    linarith
  have htbUpper : t - taoCaseThreeLeftB < (611 / 1000 : ℝ) := by
    unfold taoCaseThreeLeftB
    linarith
  have hA : -taoCaseThreeA / (t - taoCaseThreeLeftA) <
      -taoCaseThreeA / (9 / 10 : ℝ) := by
    have hinv := one_div_lt_one_div_of_lt htaPos htaUpper
    have hmul := mul_lt_mul_of_pos_left hinv
      (show 0 < taoCaseThreeA by norm_num [taoCaseThreeA])
    convert! neg_lt_neg hmul using 1 <;> ring
  have hB : -taoCaseThreeB / (t - taoCaseThreeLeftB) <
      -taoCaseThreeB / (611 / 1000 : ℝ) := by
    have hinv := one_div_lt_one_div_of_lt htbPos htbUpper
    have hmul := mul_lt_mul_of_pos_left hinv
      (show 0 < taoCaseThreeB by norm_num [taoCaseThreeB])
    convert! neg_lt_neg hmul using 1 <;> ring
  have hbase : (25 / 121 : ℝ) + 7 / 20 -
      taoCaseThreeA / (9 / 10) -
      taoCaseThreeB / (611 / 1000) < 0 := by
    norm_num [taoCaseThreeA, taoCaseThreeB]
  dsimp only [K] at hcombined
  ring_nf at hcombined hfirst hA hB hbase ⊢
  linarith

theorem taoCaseThreePotentialSecondDerivative_neg_of_right
    {t : ℝ} (ht : t ∈ Ioo taoCaseThreeLeftB (253 / 100 : ℝ)) :
    taoCaseThreePotentialSecondDerivative t < 0 := by
  by_cases hsplit : t ≤ (11 / 5 : ℝ)
  · exact taoCaseThreePotentialSecondDerivative_neg_of_right_low
      ht.1 hsplit
  · exact taoCaseThreePotentialSecondDerivative_neg_of_right_high
      (le_of_not_ge hsplit) ht.2

theorem taoCaseThreePotential_concaveOn_right :
    ConcaveOn ℝ (Icc taoCaseThreeLeftB (253 / 100 : ℝ))
      taoCaseThreePotential := by
  apply concaveOn_of_deriv2_nonpos (convex_Icc _ _)
  · exact continuousOn_taoCaseThreePotential_input.mono fun _ ht ↦ by
      constructor
      · have hfloor : taoCaseThreeInputFloor < taoCaseThreeLeftB := by
          norm_num [taoCaseThreeInputFloor, taoCaseThreeLeftB]
        exact hfloor.le.trans ht.1
      · have hceiling : (253 / 100 : ℝ) < taoCaseThreeInputCeiling := by
          norm_num [taoCaseThreeInputCeiling]
        exact ht.2.trans hceiling.le
  · rw [interior_Icc]
    intro t ht
    have hMbound : (253 / 100 : ℝ) < taoUpperEdge := by
      unfold taoUpperEdge
      nlinarith [seven_fifths_lt_sqrt_two]
    exact (hasDerivAt_taoCaseThreePotential
      (by
        have h : 0 < taoCaseThreeLeftB := by
          norm_num [taoCaseThreeLeftB]
        exact (h.trans ht.1).ne')
      (sub_pos.mpr (ht.2.trans hMbound)).ne'
      (sub_neg.mpr (tao_case_three_leftA_lt_leftB.trans ht.1)).ne
      (sub_neg.mpr ht.1).ne
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    have hMbound : (253 / 100 : ℝ) < taoUpperEdge := by
      unfold taoUpperEdge
      nlinarith [seven_fifths_lt_sqrt_two]
    exact (hasDerivAt_deriv_taoCaseThreePotential
      (by
        have h : 0 < taoCaseThreeLeftB := by
          norm_num [taoCaseThreeLeftB]
        exact (h.trans ht.1).ne')
      (sub_pos.mpr (ht.2.trans hMbound)).ne'
      (sub_neg.mpr (tao_case_three_leftA_lt_leftB.trans ht.1)).ne
      (sub_neg.mpr ht.1).ne
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    have hMbound : (253 / 100 : ℝ) < taoUpperEdge := by
      unfold taoUpperEdge
      nlinarith [seven_fifths_lt_sqrt_two]
    rw [deriv2_taoCaseThreePotential
      (by
        have h : 0 < taoCaseThreeLeftB := by
          norm_num [taoCaseThreeLeftB]
        exact (h.trans ht.1).ne')
      (sub_pos.mpr (ht.2.trans hMbound)).ne'
      (sub_neg.mpr (tao_case_three_leftA_lt_leftB.trans ht.1)).ne
      (sub_neg.mpr ht.1).ne]
    exact (taoCaseThreePotentialSecondDerivative_neg_of_right ht).le

theorem taoCaseThreePotentialSecondDerivative_pos_of_upper
    {t : ℝ} (ht : t ∈ Ioo (51 / 20 : ℝ)
      taoCaseThreeInputCeiling) :
    0 < taoCaseThreePotentialSecondDerivative t := by
  have htPos : 0 < t :=
    (by norm_num : (0 : ℝ) < 51 / 20).trans ht.1
  have hMPos : 0 < taoUpperEdge - t :=
    sub_pos.mpr (ht.2.trans tao_case_three_inputCeiling_lt_upperEdge)
  have htaPos : 0 < t - taoCaseThreeLeftA := by
    norm_num [taoCaseThreeLeftA] at ht ⊢
    linarith [ht.1]
  have htbPos : 0 < t - taoCaseThreeLeftB := by
    norm_num [taoCaseThreeLeftB] at ht ⊢
    linarith [ht.1]
  rw [taoCaseThreePotentialSecondDerivative_eq_right]
  let K : ℝ := taoCaseThreeA + taoCaseThreeB
  let U : ℝ := 6961 / 25000
  have hKpos : 0 < K := by
    dsimp only [K]
    norm_num [taoCaseThreeA, taoCaseThreeB]
  have hUpos : 0 < U := by
    dsimp only [U]
    norm_num
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hsqrtNonneg := Real.sqrt_nonneg 2
  have hsqrtUpper : Real.sqrt 2 < (70711 / 50000 : ℝ) := by
    nlinarith
  have huUpper : taoUpperEdge - t < U := by
    dsimp only [U]
    unfold taoUpperEdge
    linarith [ht.1, hsqrtUpper]
  have huSq : (taoUpperEdge - t) ^ 2 < U ^ 2 := by
    nlinarith
  have hnumU : 0 < taoCaseThreeC - K * U := by
    dsimp only [K, U]
    norm_num [taoCaseThreeA, taoCaseThreeB, taoCaseThreeC]
  have hnum : taoCaseThreeC - K * U <
      taoCaseThreeC - K * (taoUpperEdge - t) := by
    nlinarith
  have hinvSq : 1 / U ^ 2 < 1 / (taoUpperEdge - t) ^ 2 :=
    one_div_lt_one_div_of_lt (sq_pos_of_pos hMPos) huSq
  have hcombined :
      taoCaseThreeC / U ^ 2 - K / U <
        taoCaseThreeC / (taoUpperEdge - t) ^ 2 -
          K / (taoUpperEdge - t) := by
    rw [show taoCaseThreeC / U ^ 2 - K / U =
        (taoCaseThreeC - K * U) / U ^ 2 by
          field_simp [hUpos.ne']
      , show taoCaseThreeC / (taoUpperEdge - t) ^ 2 -
          K / (taoUpperEdge - t) =
        (taoCaseThreeC - K * (taoUpperEdge - t)) /
          (taoUpperEdge - t) ^ 2 by
          field_simp [hMPos.ne']]
    have hfirstStep :
        (taoCaseThreeC - K * U) / U ^ 2 <
          (taoCaseThreeC - K * U) /
            (taoUpperEdge - t) ^ 2 := by
      simpa only [div_eq_mul_inv, one_mul] using!
        mul_lt_mul_of_pos_left hinvSq hnumU
    have hsecondStep :
        (taoCaseThreeC - K * U) /
            (taoUpperEdge - t) ^ 2 <
          (taoCaseThreeC - K * (taoUpperEdge - t)) /
            (taoUpperEdge - t) ^ 2 := by
      exact div_lt_div_of_pos_right hnum
        (sq_pos_of_pos hMPos)
    exact hfirstStep.trans hsecondStep
  have htSq : t ^ 2 < 8 := by
    have hMPos' : 0 < taoUpperEdge := by
      unfold taoUpperEdge
      positivity
    have htM : t < taoUpperEdge :=
      ht.2.trans tao_case_three_inputCeiling_lt_upperEdge
    have hMsq : taoUpperEdge ^ 2 = 8 := by
      unfold taoUpperEdge
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    nlinarith
  have hfirst : (1 / 8 : ℝ) < 1 / t ^ 2 := by
    have h := one_div_lt_one_div_of_lt (sq_pos_of_pos htPos) htSq
    norm_num at h ⊢
    exact h
  have htaLower : (51 / 20 : ℝ) - taoCaseThreeLeftA <
      t - taoCaseThreeLeftA := by linarith [ht.1]
  have htbLower : (51 / 20 : ℝ) - taoCaseThreeLeftB <
      t - taoCaseThreeLeftB := by linarith [ht.1]
  have hA : -taoCaseThreeA /
        ((51 / 20 : ℝ) - taoCaseThreeLeftA) <
      -taoCaseThreeA / (t - taoCaseThreeLeftA) := by
    have hinv := one_div_lt_one_div_of_lt (by
      norm_num [taoCaseThreeLeftA]) htaLower
    have hmul := mul_lt_mul_of_pos_left hinv
      (show 0 < taoCaseThreeA by norm_num [taoCaseThreeA])
    convert! neg_lt_neg hmul using 1 <;> ring
  have hB : -taoCaseThreeB /
        ((51 / 20 : ℝ) - taoCaseThreeLeftB) <
      -taoCaseThreeB / (t - taoCaseThreeLeftB) := by
    have hinv := one_div_lt_one_div_of_lt (by
      norm_num [taoCaseThreeLeftB]) htbLower
    have hmul := mul_lt_mul_of_pos_left hinv
      (show 0 < taoCaseThreeB by norm_num [taoCaseThreeB])
    convert! neg_lt_neg hmul using 1 <;> ring
  have hbase : 0 < (1 / 8 : ℝ) -
      taoCaseThreeA / ((51 / 20 : ℝ) - taoCaseThreeLeftA) -
      taoCaseThreeB / ((51 / 20 : ℝ) - taoCaseThreeLeftB) +
      (taoCaseThreeC / U ^ 2 - K / U) := by
    dsimp only [K, U]
    norm_num [taoCaseThreeA, taoCaseThreeB, taoCaseThreeC,
      taoCaseThreeLeftA, taoCaseThreeLeftB]
  dsimp only [K] at hcombined ⊢
  ring_nf at hcombined hfirst hA hB hbase ⊢
  linarith

theorem taoCaseThreePotential_convexOn_upper :
    ConvexOn ℝ (Icc (51 / 20 : ℝ) taoCaseThreeInputCeiling)
      taoCaseThreePotential := by
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _)
  · exact continuousOn_taoCaseThreePotential_input.mono fun _ ht ↦
      ⟨(by
        have h : taoCaseThreeInputFloor ≤ (51 / 20 : ℝ) := by
          norm_num [taoCaseThreeInputFloor]
        exact h.trans ht.1), ht.2⟩
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_taoCaseThreePotential
      ((by norm_num : (0 : ℝ) < 51 / 20).trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans
        tao_case_three_inputCeiling_lt_upperEdge)).ne'
      (sub_neg.mpr (by
        have h : taoCaseThreeLeftA < (51 / 20 : ℝ) := by
          norm_num [taoCaseThreeLeftA]
        exact h.trans ht.1)).ne
      (sub_neg.mpr (by
        have h : taoCaseThreeLeftB < (51 / 20 : ℝ) := by
          norm_num [taoCaseThreeLeftB]
        exact h.trans ht.1)).ne
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_deriv_taoCaseThreePotential
      ((by norm_num : (0 : ℝ) < 51 / 20).trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans
        tao_case_three_inputCeiling_lt_upperEdge)).ne'
      (sub_neg.mpr (by
        have h : taoCaseThreeLeftA < (51 / 20 : ℝ) := by
          norm_num [taoCaseThreeLeftA]
        exact h.trans ht.1)).ne
      (sub_neg.mpr (by
        have h : taoCaseThreeLeftB < (51 / 20 : ℝ) := by
          norm_num [taoCaseThreeLeftB]
        exact h.trans ht.1)).ne
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [deriv2_taoCaseThreePotential
      ((by norm_num : (0 : ℝ) < 51 / 20).trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans
        tao_case_three_inputCeiling_lt_upperEdge)).ne'
      (sub_neg.mpr (by
        have h : taoCaseThreeLeftA < (51 / 20 : ℝ) := by
          norm_num [taoCaseThreeLeftA]
        exact h.trans ht.1)).ne
      (sub_neg.mpr (by
        have h : taoCaseThreeLeftB < (51 / 20 : ℝ) := by
          norm_num [taoCaseThreeLeftB]
        exact h.trans ht.1)).ne]
    exact (taoCaseThreePotentialSecondDerivative_pos_of_upper ht).le

end

end WangTrial

end

section
namespace WangTrial

noncomputable section

namespace RatInterval

def abs? (I : RatInterval) : Option RatInterval :=
  if 0 ≤ I.lo then some I
  else if I.hi ≤ 0 then some (neg I)
  else none

theorem abs_contains {I J : RatInterval} {x : ℝ}
    (hx : I.Contains x) (h : abs? I = some J) :
    J.Contains |x| := by
  by_cases hlo : 0 ≤ I.lo
  · rw [abs?, if_pos hlo] at h
    cases h
    have hloReal : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hlo
    rw [abs_of_nonneg (hloReal.trans hx.1)]
    exact hx
  · rw [abs?, if_neg hlo] at h
    by_cases hhi : I.hi ≤ 0
    · rw [if_pos hhi] at h
      cases h
      have hhiReal : (I.hi : ℝ) ≤ 0 := by exact_mod_cast hhi
      rw [abs_of_nonpos (hx.2.trans hhiReal)]
      exact neg_contains hx
    · simp only [if_neg hhi, reduceCtorEq] at h

end RatInterval

def evalTaoLogPrimitiveInterval
    (precision : Nat) (X : RatInterval) : Option RatInterval := do
  let AX ← RatInterval.abs? X
  let LX ← RatInterval.log? precision AX
  pure (RatInterval.sub X (RatInterval.mul X LX))

theorem evalTaoLogPrimitiveInterval_contains
    {precision : Nat} {X R : RatInterval} {x : ℝ}
    (hX : X.Contains x)
    (hEval : evalTaoLogPrimitiveInterval precision X = some R) :
    R.Contains (taoLogPrimitive x) := by
  cases hAX : RatInterval.abs? X with
  | none => simp [evalTaoLogPrimitiveInterval, hAX] at hEval
  | some AX =>
      cases hLX : RatInterval.log? precision AX with
      | none => simp [evalTaoLogPrimitiveInterval, hAX, hLX] at hEval
      | some LX =>
          simp [evalTaoLogPrimitiveInterval, hAX, hLX] at hEval
          subst R
          have hAbs := RatInterval.abs_contains hX hAX
          have hLog := RatInterval.log_contains hAbs hLX
          have hMul := RatInterval.mul_contains hX hLog
          simpa only [taoLogPrimitive] using!
            RatInterval.sub_contains hX hMul

def evalTaoCaseThreePotentialInterval
    (precision : Nat) (T : RatInterval) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let logT ← RatInterval.log? precision T
  let FM ← evalTaoLogPrimitiveInterval precision (RatInterval.sub M T)
  let Fa ← evalTaoLogPrimitiveInterval precision
    (RatInterval.sub (RatInterval.point (163 / 100)) T)
  let Fb ← evalTaoLogPrimitiveInterval precision
    (RatInterval.sub (RatInterval.point (1919 / 1000)) T)
  let absM ← RatInterval.abs? (RatInterval.sub M T)
  let logM ← RatInterval.log? precision absM
  pure (RatInterval.sub
    (RatInterval.add
      (RatInterval.add (RatInterval.neg logT)
        (RatInterval.mul (RatInterval.point (192829 / 1000000))
          (RatInterval.sub FM Fa)))
      (RatInterval.mul (RatInterval.point (28 / 125))
        (RatInterval.sub FM Fb)))
    (RatInterval.mul (RatInterval.point (31 / 200)) logM))

end

end WangTrial

end

section
namespace WangTrial

noncomputable section

theorem evalTaoCaseThreePotentialInterval_contains
    {precision : Nat} {T R : RatInterval} {t : ℝ}
    (hT : T.Contains t)
    (hEval : evalTaoCaseThreePotentialInterval precision T = some R) :
    R.Contains (taoCaseThreePotential t) := by
  cases hS : RatInterval.sqrt? precision (RatInterval.point 2) with
  | none => simp [evalTaoCaseThreePotentialInterval, hS] at hEval
  | some S =>
      let M := RatInterval.mul (RatInterval.point 2) S
      cases hlogT : RatInterval.log? precision T with
      | none =>
          simp [evalTaoCaseThreePotentialInterval, hS, hlogT] at hEval
      | some logT =>
          cases hFM : evalTaoLogPrimitiveInterval precision
              (RatInterval.sub M T) with
          | none =>
              simp [evalTaoCaseThreePotentialInterval, hS, M,
                hlogT, hFM] at hEval
          | some FM =>
              let XA := RatInterval.sub (RatInterval.point (163 / 100)) T
              cases hFa : evalTaoLogPrimitiveInterval precision XA with
              | none =>
                  simp [evalTaoCaseThreePotentialInterval, hS,
                    hlogT, XA, hFa] at hEval
              | some Fa =>
                  let XB := RatInterval.sub
                    (RatInterval.point (1919 / 1000)) T
                  cases hFb : evalTaoLogPrimitiveInterval precision XB with
                  | none =>
                      simp [evalTaoCaseThreePotentialInterval, hS,
                        hlogT, XA, hFa, XB, hFb] at hEval
                  | some Fb =>
                      cases hAbsM : RatInterval.abs?
                          (RatInterval.sub M T) with
                      | none =>
                          simp [evalTaoCaseThreePotentialInterval, hS, M,
                            hlogT, hFM, XA, hFa, XB, hFb,
                            hAbsM] at hEval
                      | some absM =>
                          cases hLogM : RatInterval.log? precision absM with
                          | none =>
                              simp [evalTaoCaseThreePotentialInterval, hS,
                                M, hlogT, hFM, XA, hFa, XB, hFb,
                                hAbsM, hLogM] at hEval
                          | some logM =>
                              simp [evalTaoCaseThreePotentialInterval, hS,
                                M, hlogT, hFM, XA, hFa, XB, hFb,
                                hAbsM, hLogM] at hEval
                              subst R
                              have hSContains := RatInterval.sqrt_contains
                                (RatInterval.point_contains (2 : Rat)) hS
                              have hM : M.Contains taoUpperEdge := by
                                simpa only [M, taoUpperEdge,
                                  Rat.cast_ofNat] using!
                                  RatInterval.mul_contains
                                    (RatInterval.point_contains (2 : Rat))
                                    hSContains
                              have hMT := RatInterval.sub_contains hM hT
                              have hFMContains :=
                                evalTaoLogPrimitiveInterval_contains hMT hFM
                              have hA :
                                  (RatInterval.point (163 / 100)).Contains
                                    taoCaseThreeLeftA := by
                                simpa only [taoCaseThreeLeftA, Rat.cast_div,
                                  Rat.cast_ofNat] using!
                                  RatInterval.point_contains (163 / 100 : Rat)
                              have hB :
                                  (RatInterval.point (1919 / 1000)).Contains
                                    taoCaseThreeLeftB := by
                                simpa only [taoCaseThreeLeftB, Rat.cast_div,
                                  Rat.cast_ofNat] using!
                                  RatInterval.point_contains
                                    (1919 / 1000 : Rat)
                              have hFaContains :=
                                evalTaoLogPrimitiveInterval_contains
                                  (RatInterval.sub_contains hA hT) hFa
                              have hFbContains :=
                                evalTaoLogPrimitiveInterval_contains
                                  (RatInterval.sub_contains hB hT) hFb
                              have hlogTContains :=
                                RatInterval.log_contains hT hlogT
                              have hlogMContains := RatInterval.log_contains
                                (RatInterval.abs_contains hMT hAbsM) hLogM
                              have hWeightA :
                                  (RatInterval.point
                                    (192829 / 1000000)).Contains
                                      taoCaseThreeA := by
                                simpa only [taoCaseThreeA, Rat.cast_div,
                                  Rat.cast_ofNat] using!
                                  RatInterval.point_contains
                                    (192829 / 1000000 : Rat)
                              have hWeightB :
                                  (RatInterval.point (28 / 125)).Contains
                                    taoCaseThreeB := by
                                simpa only [taoCaseThreeB, Rat.cast_div,
                                  Rat.cast_ofNat] using!
                                  RatInterval.point_contains (28 / 125 : Rat)
                              have hWeightC :
                                  (RatInterval.point (31 / 200)).Contains
                                    taoCaseThreeC := by
                                simpa only [taoCaseThreeC, Rat.cast_div,
                                  Rat.cast_ofNat] using!
                                  RatInterval.point_contains (31 / 200 : Rat)
                              have hValue := RatInterval.sub_contains
                                (RatInterval.add_contains
                                  (RatInterval.add_contains
                                    (RatInterval.neg_contains hlogTContains)
                                    (RatInterval.mul_contains hWeightA
                                      (RatInterval.sub_contains hFMContains
                                        hFaContains)))
                                  (RatInterval.mul_contains hWeightB
                                    (RatInterval.sub_contains hFMContains
                                      hFbContains)))
                                (RatInterval.mul_contains hWeightC
                                  hlogMContains)
                              simpa only [taoCaseThreePotential] using! hValue

theorem taoCaseThreePotential_neg_of_interval_certificate
    {precision : Nat} {T : RatInterval} {t : ℝ}
    (hT : T.Contains t)
    (hcert : ∃ R,
      evalTaoCaseThreePotentialInterval precision T = some R ∧ R.hi < 0) :
    taoCaseThreePotential t < 0 := by
  obtain ⟨R, hEval, hhi⟩ := hcert
  have hContains := evalTaoCaseThreePotentialInterval_contains hT hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact hContains.2.trans_lt hhiReal

def evalTaoCaseThreeDerivativeInterval
    (precision : Nat) (T : RatInterval) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let invT ← RatInterval.inv? T
  let MT := RatInterval.sub M T
  let absM ← RatInterval.abs? MT
  let logM ← RatInterval.log? precision absM
  let absA ← RatInterval.abs?
    (RatInterval.sub (RatInterval.point (163 / 100)) T)
  let logA ← RatInterval.log? precision absA
  let absB ← RatInterval.abs?
    (RatInterval.sub (RatInterval.point (1919 / 1000)) T)
  let logB ← RatInterval.log? precision absB
  let invM ← RatInterval.inv? MT
  pure (RatInterval.add
    (RatInterval.add
      (RatInterval.add (RatInterval.neg invT)
        (RatInterval.mul (RatInterval.point (192829 / 1000000))
          (RatInterval.sub logM logA)))
      (RatInterval.mul (RatInterval.point (28 / 125))
        (RatInterval.sub logM logB)))
    (RatInterval.mul (RatInterval.point (31 / 200)) invM))

theorem evalTaoCaseThreeDerivativeInterval_contains
    {precision : Nat} {T R : RatInterval} {t : ℝ}
    (hT : T.Contains t)
    (hEval : evalTaoCaseThreeDerivativeInterval precision T = some R) :
    R.Contains (taoCaseThreePotentialDerivative t) := by
  cases hS : RatInterval.sqrt? precision (RatInterval.point 2) with
  | none => simp [evalTaoCaseThreeDerivativeInterval, hS] at hEval
  | some S =>
      let M := RatInterval.mul (RatInterval.point 2) S
      cases hInvT : RatInterval.inv? T with
      | none =>
          simp [evalTaoCaseThreeDerivativeInterval, hS, hInvT] at hEval
      | some invT =>
          let MT := RatInterval.sub M T
          cases hAbsM : RatInterval.abs? MT with
          | none =>
              simp [evalTaoCaseThreeDerivativeInterval, hS, M, MT,
                hInvT, hAbsM] at hEval
          | some absM =>
              cases hLogM : RatInterval.log? precision absM with
              | none =>
                  simp [evalTaoCaseThreeDerivativeInterval, hS, M, MT,
                    hInvT, hAbsM, hLogM] at hEval
              | some logM =>
                  let XA := RatInterval.sub
                    (RatInterval.point (163 / 100)) T
                  cases hAbsA : RatInterval.abs? XA with
                  | none =>
                      simp [evalTaoCaseThreeDerivativeInterval, hS,
                        hInvT, XA, hAbsA] at hEval
                  | some absA =>
                      cases hLogA : RatInterval.log? precision absA with
                      | none =>
                          simp [evalTaoCaseThreeDerivativeInterval, hS,
                            hInvT, XA, hAbsA,
                            hLogA] at hEval
                      | some logA =>
                          let XB := RatInterval.sub
                            (RatInterval.point (1919 / 1000)) T
                          cases hAbsB : RatInterval.abs? XB with
                          | none =>
                              simp [evalTaoCaseThreeDerivativeInterval,
                                hS, hInvT, XA,
                                hAbsA, XB, hAbsB] at hEval
                          | some absB =>
                              cases hLogB : RatInterval.log? precision absB with
                              | none =>
                                  simp [evalTaoCaseThreeDerivativeInterval,
                                    hS, hInvT, XA,
                                    hAbsA, XB, hAbsB,
                                    hLogB] at hEval
                              | some logB =>
                                  cases hInvM : RatInterval.inv? MT with
                                  | none =>
                                      simp [evalTaoCaseThreeDerivativeInterval,
                                        hS, M, MT, hInvT, hAbsM,
                                        XA, hAbsA, hLogA, XB, hAbsB,
                                        hLogB, hInvM] at hEval
                                  | some invM =>
                                      simp [evalTaoCaseThreeDerivativeInterval,
                                        hS, M, MT, hInvT, hAbsM, hLogM,
                                        XA, hAbsA, hLogA, XB, hAbsB,
                                        hLogB, hInvM] at hEval
                                      subst R
                                      have hSContains :=
                                        RatInterval.sqrt_contains
                                          (RatInterval.point_contains
                                            (2 : Rat)) hS
                                      have hM : M.Contains taoUpperEdge := by
                                        simpa only [M, taoUpperEdge,
                                          Rat.cast_ofNat] using!
                                          RatInterval.mul_contains
                                            (RatInterval.point_contains
                                              (2 : Rat)) hSContains
                                      have hMT := RatInterval.sub_contains hM hT
                                      have hA :
                                          (RatInterval.point (163 / 100)).Contains
                                            taoCaseThreeLeftA := by
                                        simpa only [taoCaseThreeLeftA,
                                          Rat.cast_div, Rat.cast_ofNat] using!
                                          RatInterval.point_contains
                                            (163 / 100 : Rat)
                                      have hB :
                                          (RatInterval.point
                                            (1919 / 1000)).Contains
                                              taoCaseThreeLeftB := by
                                        simpa only [taoCaseThreeLeftB,
                                          Rat.cast_div, Rat.cast_ofNat] using!
                                          RatInterval.point_contains
                                            (1919 / 1000 : Rat)
                                      have hlogMContains :=
                                        RatInterval.log_contains
                                          (RatInterval.abs_contains hMT hAbsM)
                                          hLogM
                                      have hlogAContains :=
                                        RatInterval.log_contains
                                          (RatInterval.abs_contains
                                            (RatInterval.sub_contains hA hT)
                                            hAbsA) hLogA
                                      have hlogBContains :=
                                        RatInterval.log_contains
                                          (RatInterval.abs_contains
                                            (RatInterval.sub_contains hB hT)
                                            hAbsB) hLogB
                                      have hInvTContains :=
                                        RatInterval.inv_contains hT hInvT
                                      have hInvMContains :=
                                        RatInterval.inv_contains hMT hInvM
                                      have hWeightA :
                                          (RatInterval.point
                                            (192829 / 1000000)).Contains
                                              taoCaseThreeA := by
                                        simpa only [taoCaseThreeA,
                                          Rat.cast_div, Rat.cast_ofNat] using!
                                          RatInterval.point_contains
                                            (192829 / 1000000 : Rat)
                                      have hWeightB :
                                          (RatInterval.point (28 / 125)).Contains
                                            taoCaseThreeB := by
                                        simpa only [taoCaseThreeB,
                                          Rat.cast_div, Rat.cast_ofNat] using!
                                          RatInterval.point_contains
                                            (28 / 125 : Rat)
                                      have hWeightC :
                                          (RatInterval.point (31 / 200)).Contains
                                            taoCaseThreeC := by
                                        simpa only [taoCaseThreeC,
                                          Rat.cast_div, Rat.cast_ofNat] using!
                                          RatInterval.point_contains
                                            (31 / 200 : Rat)
                                      have hValue := RatInterval.add_contains
                                        (RatInterval.add_contains
                                          (RatInterval.add_contains
                                            (RatInterval.neg_contains
                                              hInvTContains)
                                            (RatInterval.mul_contains hWeightA
                                              (RatInterval.sub_contains
                                                hlogMContains
                                                hlogAContains)))
                                          (RatInterval.mul_contains hWeightB
                                            (RatInterval.sub_contains
                                              hlogMContains hlogBContains)))
                                        (RatInterval.mul_contains hWeightC
                                          hInvMContains)
                                      simpa only [taoCaseThreePotentialDerivative,
                                        neg_div, one_div, one_mul] using! hValue

def evalTaoCaseThreePotentialAtLeftA
    (precision : Nat) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let A0 := RatInterval.point (163 / 100)
  let B0 := RatInterval.point (1919 / 1000)
  let logA ← RatInterval.log? precision A0
  let FM ← evalTaoLogPrimitiveInterval precision (RatInterval.sub M A0)
  let FB ← evalTaoLogPrimitiveInterval precision (RatInterval.sub B0 A0)
  let absM ← RatInterval.abs? (RatInterval.sub M A0)
  let logM ← RatInterval.log? precision absM
  pure (RatInterval.sub
    (RatInterval.add
      (RatInterval.add (RatInterval.neg logA)
        (RatInterval.mul (RatInterval.point (192829 / 1000000)) FM))
      (RatInterval.mul (RatInterval.point (28 / 125))
        (RatInterval.sub FM FB)))
    (RatInterval.mul (RatInterval.point (31 / 200)) logM))

theorem evalTaoCaseThreePotentialAtLeftA_contains
    {precision : Nat} {R : RatInterval}
    (hEval : evalTaoCaseThreePotentialAtLeftA precision = some R) :
    R.Contains (taoCaseThreePotential taoCaseThreeLeftA) := by
  cases hS : RatInterval.sqrt? precision (RatInterval.point 2) with
  | none => simp [evalTaoCaseThreePotentialAtLeftA, hS] at hEval
  | some S =>
      let M := RatInterval.mul (RatInterval.point 2) S
      let A0 := RatInterval.point (163 / 100)
      let B0 := RatInterval.point (1919 / 1000)
      cases hlogA : RatInterval.log? precision A0 with
      | none =>
          simp [evalTaoCaseThreePotentialAtLeftA, hS, A0, hlogA] at hEval
      | some logA =>
          cases hFM : evalTaoLogPrimitiveInterval precision
              (RatInterval.sub M A0) with
          | none =>
              simp [evalTaoCaseThreePotentialAtLeftA, hS, M, A0,
                hlogA, hFM] at hEval
          | some FM =>
              cases hFB : evalTaoLogPrimitiveInterval precision
                  (RatInterval.sub B0 A0) with
              | none =>
                  simp [evalTaoCaseThreePotentialAtLeftA, hS, A0,
                    B0, hlogA, hFB] at hEval
              | some FB =>
                  cases hAbsM : RatInterval.abs?
                      (RatInterval.sub M A0) with
                  | none =>
                      simp [evalTaoCaseThreePotentialAtLeftA, hS, M, A0,
                        B0, hlogA, hFM, hFB, hAbsM] at hEval
                  | some absM =>
                      cases hLogM : RatInterval.log? precision absM with
                      | none =>
                          simp [evalTaoCaseThreePotentialAtLeftA, hS, M,
                            A0, B0, hlogA, hFM, hFB, hAbsM,
                            hLogM] at hEval
                      | some logM =>
                          simp [evalTaoCaseThreePotentialAtLeftA, hS, M,
                            A0, B0, hlogA, hFM, hFB, hAbsM,
                            hLogM] at hEval
                          subst R
                          have hSContains := RatInterval.sqrt_contains
                            (RatInterval.point_contains (2 : Rat)) hS
                          have hM : M.Contains taoUpperEdge := by
                            simpa only [M, taoUpperEdge, Rat.cast_ofNat] using!
                              RatInterval.mul_contains
                                (RatInterval.point_contains (2 : Rat))
                                hSContains
                          have hA : A0.Contains taoCaseThreeLeftA := by
                            simpa only [A0, taoCaseThreeLeftA, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (163 / 100 : Rat)
                          have hB : B0.Contains taoCaseThreeLeftB := by
                            simpa only [B0, taoCaseThreeLeftB, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (1919 / 1000 : Rat)
                          have hFMContains :=
                            evalTaoLogPrimitiveInterval_contains
                              (RatInterval.sub_contains hM hA) hFM
                          have hFBContains :=
                            evalTaoLogPrimitiveInterval_contains
                              (RatInterval.sub_contains hB hA) hFB
                          have hlogAContains :=
                            RatInterval.log_contains hA hlogA
                          have hlogMContains := RatInterval.log_contains
                            (RatInterval.abs_contains
                              (RatInterval.sub_contains hM hA) hAbsM) hLogM
                          have hWeightA :
                              (RatInterval.point
                                (192829 / 1000000)).Contains
                                  taoCaseThreeA := by
                            simpa only [taoCaseThreeA, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (192829 / 1000000 : Rat)
                          have hWeightB :
                              (RatInterval.point (28 / 125)).Contains
                                taoCaseThreeB := by
                            simpa only [taoCaseThreeB, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (28 / 125 : Rat)
                          have hWeightC :
                              (RatInterval.point (31 / 200)).Contains
                                taoCaseThreeC := by
                            simpa only [taoCaseThreeC, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (31 / 200 : Rat)
                          have hValue := RatInterval.sub_contains
                            (RatInterval.add_contains
                              (RatInterval.add_contains
                                (RatInterval.neg_contains hlogAContains)
                                (RatInterval.mul_contains hWeightA
                                  hFMContains))
                              (RatInterval.mul_contains hWeightB
                                (RatInterval.sub_contains hFMContains
                                  hFBContains)))
                            (RatInterval.mul_contains hWeightC hlogMContains)
                          convert! hValue using 1
                          unfold taoCaseThreePotential
                          rw [sub_self, taoLogPrimitive_zero]
                          ring

def evalTaoCaseThreePotentialAtLeftB
    (precision : Nat) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let A0 := RatInterval.point (163 / 100)
  let B0 := RatInterval.point (1919 / 1000)
  let logB ← RatInterval.log? precision B0
  let FM ← evalTaoLogPrimitiveInterval precision (RatInterval.sub M B0)
  let FA ← evalTaoLogPrimitiveInterval precision (RatInterval.sub A0 B0)
  let absM ← RatInterval.abs? (RatInterval.sub M B0)
  let logM ← RatInterval.log? precision absM
  pure (RatInterval.sub
    (RatInterval.add
      (RatInterval.add (RatInterval.neg logB)
        (RatInterval.mul (RatInterval.point (192829 / 1000000))
          (RatInterval.sub FM FA)))
      (RatInterval.mul (RatInterval.point (28 / 125)) FM))
    (RatInterval.mul (RatInterval.point (31 / 200)) logM))

theorem evalTaoCaseThreePotentialAtLeftB_contains
    {precision : Nat} {R : RatInterval}
    (hEval : evalTaoCaseThreePotentialAtLeftB precision = some R) :
    R.Contains (taoCaseThreePotential taoCaseThreeLeftB) := by
  cases hS : RatInterval.sqrt? precision (RatInterval.point 2) with
  | none => simp [evalTaoCaseThreePotentialAtLeftB, hS] at hEval
  | some S =>
      let M := RatInterval.mul (RatInterval.point 2) S
      let A0 := RatInterval.point (163 / 100)
      let B0 := RatInterval.point (1919 / 1000)
      cases hlogB : RatInterval.log? precision B0 with
      | none =>
          simp [evalTaoCaseThreePotentialAtLeftB, hS, B0, hlogB] at hEval
      | some logB =>
          cases hFM : evalTaoLogPrimitiveInterval precision
              (RatInterval.sub M B0) with
          | none =>
              simp [evalTaoCaseThreePotentialAtLeftB, hS, M, B0,
                hlogB, hFM] at hEval
          | some FM =>
              cases hFA : evalTaoLogPrimitiveInterval precision
                  (RatInterval.sub A0 B0) with
              | none =>
                  simp [evalTaoCaseThreePotentialAtLeftB, hS, A0,
                    B0, hlogB, hFA] at hEval
              | some FA =>
                  cases hAbsM : RatInterval.abs?
                      (RatInterval.sub M B0) with
                  | none =>
                      simp [evalTaoCaseThreePotentialAtLeftB, hS, M, A0,
                        B0, hlogB, hFM, hFA, hAbsM] at hEval
                  | some absM =>
                      cases hLogM : RatInterval.log? precision absM with
                      | none =>
                          simp [evalTaoCaseThreePotentialAtLeftB, hS, M,
                            A0, B0, hlogB, hFM, hFA, hAbsM,
                            hLogM] at hEval
                      | some logM =>
                          simp [evalTaoCaseThreePotentialAtLeftB, hS, M,
                            A0, B0, hlogB, hFM, hFA, hAbsM,
                            hLogM] at hEval
                          subst R
                          have hSContains := RatInterval.sqrt_contains
                            (RatInterval.point_contains (2 : Rat)) hS
                          have hM : M.Contains taoUpperEdge := by
                            simpa only [M, taoUpperEdge, Rat.cast_ofNat] using!
                              RatInterval.mul_contains
                                (RatInterval.point_contains (2 : Rat))
                                hSContains
                          have hA : A0.Contains taoCaseThreeLeftA := by
                            simpa only [A0, taoCaseThreeLeftA, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (163 / 100 : Rat)
                          have hB : B0.Contains taoCaseThreeLeftB := by
                            simpa only [B0, taoCaseThreeLeftB, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (1919 / 1000 : Rat)
                          have hFMContains :=
                            evalTaoLogPrimitiveInterval_contains
                              (RatInterval.sub_contains hM hB) hFM
                          have hFAContains :=
                            evalTaoLogPrimitiveInterval_contains
                              (RatInterval.sub_contains hA hB) hFA
                          have hlogBContains :=
                            RatInterval.log_contains hB hlogB
                          have hlogMContains := RatInterval.log_contains
                            (RatInterval.abs_contains
                              (RatInterval.sub_contains hM hB) hAbsM) hLogM
                          have hWeightA :
                              (RatInterval.point
                                (192829 / 1000000)).Contains
                                  taoCaseThreeA := by
                            simpa only [taoCaseThreeA, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (192829 / 1000000 : Rat)
                          have hWeightB :
                              (RatInterval.point (28 / 125)).Contains
                                taoCaseThreeB := by
                            simpa only [taoCaseThreeB, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (28 / 125 : Rat)
                          have hWeightC :
                              (RatInterval.point (31 / 200)).Contains
                                taoCaseThreeC := by
                            simpa only [taoCaseThreeC, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (31 / 200 : Rat)
                          have hValue := RatInterval.sub_contains
                            (RatInterval.add_contains
                              (RatInterval.add_contains
                                (RatInterval.neg_contains hlogBContains)
                                (RatInterval.mul_contains hWeightA
                                  (RatInterval.sub_contains hFMContains
                                    hFAContains)))
                              (RatInterval.mul_contains hWeightB hFMContains))
                            (RatInterval.mul_contains hWeightC hlogMContains)
                          convert! hValue using 1
                          unfold taoCaseThreePotential
                          rw [sub_self, taoLogPrimitive_zero]
                          ring

def evalTaoCaseThreeTangentInterval
    (precision : Nat) (q x : Rat) : Option RatInterval := do
  let P ← evalTaoCaseThreePotentialInterval precision (RatInterval.point q)
  let D ← evalTaoCaseThreeDerivativeInterval precision (RatInterval.point q)
  pure (RatInterval.add P
    (RatInterval.mul D (RatInterval.point (x - q))))

theorem evalTaoCaseThreeTangentInterval_contains
    {precision : Nat} {q x : Rat} {R : RatInterval}
    (hEval : evalTaoCaseThreeTangentInterval precision q x = some R) :
    R.Contains (taoCaseThreePotential (q : ℝ) +
      taoCaseThreePotentialDerivative (q : ℝ) * ((x : ℝ) - (q : ℝ))) := by
  cases hP : evalTaoCaseThreePotentialInterval precision
      (RatInterval.point q) with
  | none => simp [evalTaoCaseThreeTangentInterval, hP] at hEval
  | some P =>
      cases hD : evalTaoCaseThreeDerivativeInterval precision
          (RatInterval.point q) with
      | none =>
          simp [evalTaoCaseThreeTangentInterval, hP, hD] at hEval
      | some D =>
          simp [evalTaoCaseThreeTangentInterval, hP, hD] at hEval
          subst R
          exact RatInterval.add_contains
            (evalTaoCaseThreePotentialInterval_contains
              (RatInterval.point_contains q) hP)
            (RatInterval.mul_contains
              (evalTaoCaseThreeDerivativeInterval_contains
                (RatInterval.point_contains q) hD)
              (by simpa only [Rat.cast_sub] using!
                RatInterval.point_contains (x - q)))

end

end WangTrial

end

section
open Set

namespace WangTrial

noncomputable section

theorem ConcaveOn.le_tangent_of_hasDerivAt
    {S : Set ℝ} {f : ℝ → ℝ} {q x d : ℝ}
    (hconc : ConcaveOn ℝ S f) (hq : q ∈ S) (hx : x ∈ S)
    (hderiv : HasDerivAt f d q) :
    f x ≤ f q + d * (x - q) := by
  rcases lt_trichotomy x q with hxq | rfl | hqx
  · have hs := hconc.deriv_le_slope hx hq hxq hderiv.differentiableAt
    rw [hderiv.deriv] at hs
    have hqsub : 0 < q - x := sub_pos.mpr hxq
    have hne : q - x ≠ 0 := hqsub.ne'
    have hslope : (q - x) * slope f x q = f q - f x := by
      rw [slope, vsub_eq_sub, smul_eq_mul]
      field_simp [hne]
    have hmul := mul_le_mul_of_nonneg_left hs hqsub.le
    rw [hslope] at hmul
    nlinarith
  · simp
  · have hs := hconc.slope_le_deriv hq hx hqx hderiv.differentiableAt
    rw [hderiv.deriv] at hs
    have hxsub : 0 < x - q := sub_pos.mpr hqx
    have hne : x - q ≠ 0 := hxsub.ne'
    have hslope : (x - q) * slope f q x = f x - f q := by
      rw [slope, vsub_eq_sub, smul_eq_mul]
      field_simp [hne]
    have hmul := mul_le_mul_of_nonneg_left hs hxsub.le
    rw [hslope] at hmul
    nlinarith

end

end WangTrial

end

section
open Set

namespace WangTrial

noncomputable section

def taoCaseThreeTangentPointRat : Rat := 8771 / 4000

set_option maxRecDepth 100000 in
theorem taoCaseThree_floor_certificate :
    ∃ R, evalTaoCaseThreePotentialInterval 50
      (RatInterval.point (953 / 1250)) = some R ∧ R.hi < 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem taoCaseThree_leftA_certificate :
    ∃ R, evalTaoCaseThreePotentialAtLeftA 50 = some R ∧ R.hi < 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem taoCaseThree_leftB_certificate :
    ∃ R, evalTaoCaseThreePotentialAtLeftB 50 = some R ∧ R.hi < 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem taoCaseThree_left_tangent_certificate :
    ∃ R, evalTaoCaseThreeTangentInterval 50
      taoCaseThreeTangentPointRat (1919 / 1000) = some R ∧ R.hi < 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem taoCaseThree_right_tangent_certificate :
    ∃ R, evalTaoCaseThreeTangentInterval 50
      taoCaseThreeTangentPointRat (253 / 100) = some R ∧ R.hi < 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem taoCaseThree_transition_certificate :
    ∃ R, evalTaoCaseThreePotentialInterval 50
      ⟨253 / 100, 51 / 20⟩ = some R ∧ R.hi < 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem taoCaseThree_ceiling_certificate :
    ∃ R, evalTaoCaseThreePotentialInterval 80
      (RatInterval.point (27987 / 10000)) = some R ∧ R.hi < 0 := by
  decide +kernel

theorem taoCaseThreePotential_floor_neg :
    taoCaseThreePotential taoCaseThreeInputFloor < 0 := by
  have hPoint := RatInterval.point_contains (953 / 1250 : Rat)
  have hContains :
      (RatInterval.point (953 / 1250)).Contains
        taoCaseThreeInputFloor := by
    simpa only [taoCaseThreeInputFloor, Rat.cast_div,
      Rat.cast_ofNat] using! hPoint
  exact taoCaseThreePotential_neg_of_interval_certificate
    hContains taoCaseThree_floor_certificate

theorem taoCaseThreePotential_leftA_neg :
    taoCaseThreePotential taoCaseThreeLeftA < 0 := by
  obtain ⟨R, hEval, hhi⟩ := taoCaseThree_leftA_certificate
  have hContains := evalTaoCaseThreePotentialAtLeftA_contains hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact hContains.2.trans_lt hhiReal

theorem taoCaseThreePotential_leftB_neg :
    taoCaseThreePotential taoCaseThreeLeftB < 0 := by
  obtain ⟨R, hEval, hhi⟩ := taoCaseThree_leftB_certificate
  have hContains := evalTaoCaseThreePotentialAtLeftB_contains hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact hContains.2.trans_lt hhiReal

theorem taoCaseThreePotential_ceiling_neg :
    taoCaseThreePotential taoCaseThreeInputCeiling < 0 := by
  have hPoint := RatInterval.point_contains (27987 / 10000 : Rat)
  have hContains :
      (RatInterval.point (27987 / 10000)).Contains
        taoCaseThreeInputCeiling := by
    simpa only [taoCaseThreeInputCeiling, Rat.cast_div,
      Rat.cast_ofNat] using! hPoint
  exact taoCaseThreePotential_neg_of_interval_certificate
    hContains taoCaseThree_ceiling_certificate

theorem taoCaseThreePotential_neg_on_transition :
    ∀ t ∈ Icc (253 / 100 : ℝ) (51 / 20 : ℝ),
      taoCaseThreePotential t < 0 := by
  intro t ht
  have hContains : (RatInterval.mk (253 / 100) (51 / 20)).Contains t := by
    simpa only [RatInterval.Contains, Rat.cast_div,
      Rat.cast_ofNat] using! ht
  exact taoCaseThreePotential_neg_of_interval_certificate
    hContains taoCaseThree_transition_certificate

private theorem taoCaseThree_left_tangent_neg :
    taoCaseThreePotential (taoCaseThreeTangentPointRat : ℝ) +
      taoCaseThreePotentialDerivative (taoCaseThreeTangentPointRat : ℝ) *
        (taoCaseThreeLeftB - (taoCaseThreeTangentPointRat : ℝ)) < 0 := by
  obtain ⟨R, hEval, hhi⟩ := taoCaseThree_left_tangent_certificate
  have hContains := evalTaoCaseThreeTangentInterval_contains hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  have hValue := hContains.2.trans_lt hhiReal
  simpa only [taoCaseThreeLeftB, Rat.cast_div,
    Rat.cast_ofNat] using! hValue

private theorem taoCaseThree_right_tangent_neg :
    taoCaseThreePotential (taoCaseThreeTangentPointRat : ℝ) +
      taoCaseThreePotentialDerivative (taoCaseThreeTangentPointRat : ℝ) *
        ((253 / 100 : ℝ) - (taoCaseThreeTangentPointRat : ℝ)) < 0 := by
  obtain ⟨R, hEval, hhi⟩ := taoCaseThree_right_tangent_certificate
  have hContains := evalTaoCaseThreeTangentInterval_contains hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  simpa only [Rat.cast_div, Rat.cast_ofNat] using!
    hContains.2.trans_lt hhiReal

theorem taoCaseThreePotential_neg_on_concave_right :
    ∀ t ∈ Icc taoCaseThreeLeftB (253 / 100 : ℝ),
      taoCaseThreePotential t < 0 := by
  intro t ht
  let q : ℝ := taoCaseThreeTangentPointRat
  have hqOpen : q ∈ Ioo taoCaseThreeLeftB (253 / 100 : ℝ) := by
    constructor <;>
      norm_num [q, taoCaseThreeTangentPointRat, taoCaseThreeLeftB]
  have hq : q ∈ Icc taoCaseThreeLeftB (253 / 100 : ℝ) :=
    ⟨hqOpen.1.le, hqOpen.2.le⟩
  have hqPos : 0 < q := by
    norm_num [q, taoCaseThreeTangentPointRat]
  have hM : taoUpperEdge - q ≠ 0 := by
    have hqM : q < taoUpperEdge := by
      have hqC : q < (253 / 100 : ℝ) := hqOpen.2
      have hCM : (253 / 100 : ℝ) < taoUpperEdge := by
        unfold taoUpperEdge
        nlinarith [seven_fifths_lt_sqrt_two]
      exact hqC.trans hCM
    exact (sub_pos.mpr hqM).ne'
  have ha : taoCaseThreeLeftA - q ≠ 0 := by
    have : taoCaseThreeLeftA < q :=
      tao_case_three_leftA_lt_leftB.trans hqOpen.1
    exact (sub_neg.mpr this).ne
  have hb : taoCaseThreeLeftB - q ≠ 0 :=
    (sub_neg.mpr hqOpen.1).ne
  have hderiv : HasDerivAt taoCaseThreePotential
      (taoCaseThreePotentialDerivative q) q :=
    hasDerivAt_taoCaseThreePotential hqPos.ne' hM ha hb
  have htangent := ConcaveOn.le_tangent_of_hasDerivAt
    taoCaseThreePotential_concaveOn_right hq ht hderiv
  by_cases hD : 0 ≤ taoCaseThreePotentialDerivative q
  · have hdelta : t - q ≤ (253 / 100 : ℝ) - q := by
      linarith [ht.2]
    have hmul := mul_le_mul_of_nonneg_left hdelta hD
    calc
      taoCaseThreePotential t ≤
          taoCaseThreePotential q +
            taoCaseThreePotentialDerivative q * (t - q) := htangent
      _ ≤ taoCaseThreePotential q +
          taoCaseThreePotentialDerivative q *
            ((253 / 100 : ℝ) - q) := by linarith
      _ < 0 := by
        simpa only [q] using! taoCaseThree_right_tangent_neg
  · have hDnonpos : taoCaseThreePotentialDerivative q ≤ 0 :=
      le_of_not_ge hD
    have hdelta : taoCaseThreeLeftB - q ≤ t - q := by
      linarith [ht.1]
    have hmul := mul_le_mul_of_nonpos_left hdelta hDnonpos
    calc
      taoCaseThreePotential t ≤
          taoCaseThreePotential q +
            taoCaseThreePotentialDerivative q * (t - q) := htangent
      _ ≤ taoCaseThreePotential q +
          taoCaseThreePotentialDerivative q *
            (taoCaseThreeLeftB - q) := by linarith
      _ < 0 := by
        simpa only [q] using! taoCaseThree_left_tangent_neg

theorem taoCaseThreePotential_neg_on_input :
    ∀ t ∈ Icc taoCaseThreeInputFloor taoCaseThreeInputCeiling,
      taoCaseThreePotential t < 0 := by
  intro t ht
  by_cases hta : t ≤ taoCaseThreeLeftA
  · have hle := taoCaseThreePotential_convexOn_left.le_max_of_mem_Icc
      ⟨le_rfl, tao_case_three_inputFloor_lt_leftA.le⟩
      ⟨tao_case_three_inputFloor_lt_leftA.le, le_rfl⟩
      ⟨ht.1, hta⟩
    exact hle.trans_lt (max_lt taoCaseThreePotential_floor_neg
      taoCaseThreePotential_leftA_neg)
  · have hat : taoCaseThreeLeftA < t := lt_of_not_ge hta
    by_cases htb : t ≤ taoCaseThreeLeftB
    · exact (taoCaseThreePotential_strictMonoOn_middle.monotoneOn
        ⟨hat.le, htb⟩
        ⟨tao_case_three_leftA_lt_leftB.le, le_rfl⟩ htb).trans_lt
          taoCaseThreePotential_leftB_neg
    · have hbt : taoCaseThreeLeftB < t := lt_of_not_ge htb
      by_cases htc : t ≤ (253 / 100 : ℝ)
      · exact taoCaseThreePotential_neg_on_concave_right t ⟨hbt.le, htc⟩
      · have hct : (253 / 100 : ℝ) < t := lt_of_not_ge htc
        by_cases htd : t ≤ (51 / 20 : ℝ)
        · exact taoCaseThreePotential_neg_on_transition t ⟨hct.le, htd⟩
        · have hdt : (51 / 20 : ℝ) < t := lt_of_not_ge htd
          have hDneg : taoCaseThreePotential (51 / 20 : ℝ) < 0 :=
            taoCaseThreePotential_neg_on_transition _ ⟨by norm_num, le_rfl⟩
          have hle := taoCaseThreePotential_convexOn_upper.le_max_of_mem_Icc
            ⟨le_rfl, tao_case_three_transitionHigh_lt_inputCeiling.le⟩
            ⟨tao_case_three_transitionHigh_lt_inputCeiling.le, le_rfl⟩
            ⟨hdt.le, ht.2⟩
          exact hle.trans_lt (max_lt hDneg
            taoCaseThreePotential_ceiling_neg)

end

end WangTrial

end

section
open scoped BigOperators

open MeasureTheory Set Polynomial

namespace WangTrial

noncomputable section

def taoTrialMeasurePotential (ν : Measure ℝ) (t : ℝ) : ℝ :=
  -∫ x, Real.log |t - x| ∂ν

end

end WangTrial

end

section
open scoped ENNReal Real BoundedContinuousFunction

open MeasureTheory Set Filter

namespace WangTrial

noncomputable section

def logKernel (t x : ℝ) : ℝ := Real.log |x - t|

theorem integrableOn_logKernel_Icc {a b t : ℝ} (hab : a ≤ b) :
    IntegrableOn (logKernel t) (Icc a b) volume := by
  have hlog : IntervalIntegrable Real.log volume (a - t) (b - t) :=
    intervalIntegral.intervalIntegrable_log'
  have htranslate := hlog.comp_sub_right t
  have hinterval : IntervalIntegrable (logKernel t) volume a b := by
    change IntervalIntegrable (fun x ↦ Real.log |x - t|) volume a b
    simpa only [Real.log_abs, sub_add_cancel] using! htranslate
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hinterval

section FiniteRank

variable {X E ι κ : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

end FiniteRank

section CompactFiniteRank

variable {Y F : Type*} [PseudoMetricSpace Y] [CompactSpace Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end CompactFiniteRank

end

end WangTrial

end

section
open scoped ENNReal

open MeasureTheory Set

namespace WangTrial

noncomputable section

def taoIntervalTrialMeasure (A a b : ℝ) : Measure ℝ :=
  ENNReal.ofReal A • volume.restrict (Icc a b)

def taoCaseThreeTrialMeasure : Measure ℝ :=
  Measure.dirac 0 +
    taoIntervalTrialMeasure taoCaseThreeA taoCaseThreeLeftA taoUpperEdge +
    taoIntervalTrialMeasure taoCaseThreeB taoCaseThreeLeftB taoUpperEdge +
    ENNReal.ofReal taoCaseThreeC • Measure.dirac taoUpperEdge

instance instIsFiniteMeasureTaoIntervalTrialMeasure (A a b : ℝ) :
    IsFiniteMeasure (taoIntervalTrialMeasure A a b) :=
  (volume.restrict (Icc a b)).smul_finite (by simp)

instance instIsFiniteMeasureTaoCaseThreeTrialMeasure :
    IsFiniteMeasure taoCaseThreeTrialMeasure := by
  letI : IsFiniteMeasure
      (ENNReal.ofReal taoCaseThreeC • Measure.dirac taoUpperEdge) :=
    (Measure.dirac taoUpperEdge).smul_finite (by simp)
  unfold taoCaseThreeTrialMeasure
  infer_instance

theorem taoCaseThreeTrialMeasure_singleton {s : ℝ}
    (hs0 : s ≠ 0) (hsM : s ≠ taoUpperEdge) :
    taoCaseThreeTrialMeasure {s} = 0 := by
  simp [taoCaseThreeTrialMeasure, hs0, hsM,
    taoIntervalTrialMeasure]

theorem ae_taoIntervalTrialMeasure_mem (A a b : ℝ) :
    ∀ᵐ s ∂taoIntervalTrialMeasure A a b, s ∈ Icc a b := by
  exact Measure.ae_smul_measure
    (ae_restrict_mem measurableSet_Icc) _

theorem ae_taoCaseThreeTrialMeasure_mem :
    ∀ᵐ s ∂taoCaseThreeTrialMeasure,
      s = 0 ∨ s ∈ Icc taoCaseThreeLeftA taoUpperEdge := by
  rw [taoCaseThreeTrialMeasure, ae_add_measure_iff,
    ae_add_measure_iff, ae_add_measure_iff]
  constructor
  · constructor
    · constructor
      · simp
      · exact (ae_taoIntervalTrialMeasure_mem taoCaseThreeA
          taoCaseThreeLeftA taoUpperEdge).mono
            (fun s hs ↦ Or.inr hs)
    · exact (ae_taoIntervalTrialMeasure_mem taoCaseThreeB
        taoCaseThreeLeftB taoUpperEdge).mono (fun s hs ↦
          Or.inr ⟨by
            norm_num [taoCaseThreeLeftA, taoCaseThreeLeftB] at hs ⊢
            linarith, hs.2⟩)
  · apply Measure.ae_smul_measure
    refine (ae_dirac_iff (by measurability)).2 ?_
    refine Or.inr ⟨?_, le_rfl⟩
    unfold taoCaseThreeLeftA taoUpperEdge
    nlinarith [seven_fifths_lt_sqrt_two]

theorem integrable_log_sub_taoIntervalTrialMeasure
    {A a b r : ℝ} (hab : a ≤ b) :
    Integrable (fun x : ℝ ↦ Real.log |x - r|)
      (taoIntervalTrialMeasure A a b) := by
  have hbase : Integrable (fun x : ℝ ↦ Real.log |x - r|)
      (volume.restrict (Icc a b)) := by
    simpa only [logKernel] using!
      (integrableOn_logKernel_Icc (t := r) hab)
  exact hbase.smul_measure (by simp)

theorem integrable_log_t_sub_taoIntervalTrialMeasure
    {A a b t : ℝ} (hab : a ≤ b) :
    Integrable (fun x : ℝ ↦ Real.log |t - x|)
      (taoIntervalTrialMeasure A a b) := by
  refine (integrable_log_sub_taoIntervalTrialMeasure
    (A := A) (r := t) hab).congr ?_
  filter_upwards [] with x
  rw [abs_sub_comm]

theorem taoTrialMeasurePotential_dirac (a t : ℝ) :
    taoTrialMeasurePotential (Measure.dirac a) t =
      -Real.log |t - a| := by
  simp [taoTrialMeasurePotential]

theorem taoTrialMeasurePotential_interval
    {A a b t : ℝ} (hA : 0 ≤ A) (hab : a ≤ b) :
    taoTrialMeasurePotential (taoIntervalTrialMeasure A a b) t =
      A * (∫ s in a..b, -Real.log |t - s|) := by
  unfold taoTrialMeasurePotential taoIntervalTrialMeasure
  rw [integral_smul_measure, ENNReal.toReal_ofReal hA]
  have hset :
      (∫ s, Real.log |t - s| ∂volume.restrict (Icc a b)) =
        ∫ s in a..b, Real.log |t - s| := by
    rw [intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc]
  rw [hset, intervalIntegral.integral_neg]
  simp only [smul_eq_mul]
  ring

theorem taoTrialMeasurePotential_add
    {nu mu : Measure ℝ} {t : ℝ}
    (hnu : Integrable (fun x : ℝ ↦ Real.log |t - x|) nu)
    (hmu : Integrable (fun x : ℝ ↦ Real.log |t - x|) mu) :
    taoTrialMeasurePotential (nu + mu) t =
      taoTrialMeasurePotential nu t + taoTrialMeasurePotential mu t := by
  unfold taoTrialMeasurePotential
  rw [integral_add_measure hnu hmu]
  ring

theorem taoCaseThreeA_nonnegative : 0 ≤ taoCaseThreeA := by
  norm_num [taoCaseThreeA]

theorem taoCaseThreeB_nonnegative : 0 ≤ taoCaseThreeB := by
  norm_num [taoCaseThreeB]

theorem taoCaseThreeC_nonnegative : 0 ≤ taoCaseThreeC := by
  norm_num [taoCaseThreeC]

theorem tao_case_three_leftA_le_upperEdge :
    taoCaseThreeLeftA ≤ taoUpperEdge := by
  unfold taoCaseThreeLeftA taoUpperEdge
  nlinarith [seven_fifths_lt_sqrt_two]

theorem tao_case_three_leftB_le_upperEdge :
    taoCaseThreeLeftB ≤ taoUpperEdge := by
  unfold taoCaseThreeLeftB taoUpperEdge
  nlinarith [seven_fifths_lt_sqrt_two]

theorem integrable_log_t_sub_taoCaseThreeTrialMeasure (t : ℝ) :
    Integrable (fun x : ℝ ↦ Real.log |t - x|)
      taoCaseThreeTrialMeasure := by
  unfold taoCaseThreeTrialMeasure
  apply Integrable.add_measure
  · apply Integrable.add_measure
    · apply Integrable.add_measure
      · apply integrable_dirac
        finiteness
      · exact integrable_log_t_sub_taoIntervalTrialMeasure
          tao_case_three_leftA_le_upperEdge
    · exact integrable_log_t_sub_taoIntervalTrialMeasure
        tao_case_three_leftB_le_upperEdge
  · exact (integrable_dirac (by finiteness)).smul_measure (by simp)

theorem integrable_log_sub_taoCaseThreeTrialMeasure (r : ℝ) :
    Integrable (fun x : ℝ ↦ Real.log |x - r|)
      taoCaseThreeTrialMeasure := by
  refine (integrable_log_t_sub_taoCaseThreeTrialMeasure r).congr ?_
  filter_upwards [] with x
  rw [abs_sub_comm]

theorem taoCaseThreeTrialMeasure_potential {t : ℝ} (ht : 0 < t) :
    taoTrialMeasurePotential taoCaseThreeTrialMeasure t =
      taoCaseThreePotential t := by
  let mu0 : Measure ℝ := Measure.dirac 0
  let muA : Measure ℝ :=
    taoIntervalTrialMeasure taoCaseThreeA taoCaseThreeLeftA taoUpperEdge
  let muB : Measure ℝ :=
    taoIntervalTrialMeasure taoCaseThreeB taoCaseThreeLeftB taoUpperEdge
  let muC : Measure ℝ :=
    ENNReal.ofReal taoCaseThreeC • Measure.dirac taoUpperEdge
  have h0 : Integrable (fun x : ℝ ↦ Real.log |t - x|) mu0 := by
    dsimp only [mu0]
    exact integrable_dirac (by finiteness)
  have hA : Integrable (fun x : ℝ ↦ Real.log |t - x|) muA := by
    dsimp only [muA]
    exact integrable_log_t_sub_taoIntervalTrialMeasure
      tao_case_three_leftA_le_upperEdge
  have hB : Integrable (fun x : ℝ ↦ Real.log |t - x|) muB := by
    dsimp only [muB]
    exact integrable_log_t_sub_taoIntervalTrialMeasure
      tao_case_three_leftB_le_upperEdge
  have hC : Integrable (fun x : ℝ ↦ Real.log |t - x|) muC := by
    dsimp only [muC]
    exact (integrable_dirac (by finiteness)).smul_measure (by simp)
  have hCpot : taoTrialMeasurePotential muC t =
      -taoCaseThreeC * Real.log |t - taoUpperEdge| := by
    dsimp only [muC]
    unfold taoTrialMeasurePotential
    rw [integral_smul_measure, ENNReal.toReal_ofReal
      taoCaseThreeC_nonnegative, integral_dirac]
    simp only [smul_eq_mul]
    ring
  change taoTrialMeasurePotential (((mu0 + muA) + muB) + muC) t = _
  rw [taoTrialMeasurePotential_add ((h0.add_measure hA).add_measure hB) hC,
    taoTrialMeasurePotential_add (h0.add_measure hA) hB,
    taoTrialMeasurePotential_add h0 hA,
    show taoTrialMeasurePotential mu0 t = -Real.log |t| by
      dsimp only [mu0]
      rw [taoTrialMeasurePotential_dirac, sub_zero],
    show taoTrialMeasurePotential muA t =
        taoCaseThreeA *
          (∫ s in taoCaseThreeLeftA..taoUpperEdge,
            -Real.log |t - s|) by
      dsimp only [muA]
      exact taoTrialMeasurePotential_interval taoCaseThreeA_nonnegative
        tao_case_three_leftA_le_upperEdge,
    show taoTrialMeasurePotential muB t =
        taoCaseThreeB *
          (∫ s in taoCaseThreeLeftB..taoUpperEdge,
            -Real.log |t - s|) by
      dsimp only [muB]
      exact taoTrialMeasurePotential_interval taoCaseThreeB_nonnegative
        tao_case_three_leftB_le_upperEdge,
    hCpot]
  rw [abs_of_pos ht, intervalDensityPotential_eq_primitive,
    intervalDensityPotential_eq_primitive, abs_sub_comm]
  unfold taoCaseThreePotential
  ring

end

end WangTrial

end

section
open MeasureTheory Set

namespace WangTrial

noncomputable section

theorem taoCaseThreeTrialMeasure_potential_neg
    {t0 : ℝ}
    (ht0Lower : taoCaseThreeCenterFloor ≤ t0)
    (ht0Upper : t0 ≤ taoCaseThreeCenterCeiling) :
    ∀ t ∈ Icc (t0 - 1) (t0 + 1),
      taoTrialMeasurePotential taoCaseThreeTrialMeasure t < 0 := by
  intro t ht
  have hinput := tao_case_three_center_interval_mem_input
    ht0Lower ht0Upper ht
  have htPos : 0 < t :=
    tao_case_three_inputFloor_pos.trans_le hinput.1
  rw [taoCaseThreeTrialMeasure_potential htPos]
  exact taoCaseThreePotential_neg_on_input t hinput

theorem ae_taoCaseThreeTrialMeasure_source_support
    {t0 : ℝ} (ht0Upper : t0 ≤ taoCaseThreeCenterCeiling) :
    ∀ᵐ s ∂taoCaseThreeTrialMeasure,
      s = 0 ∨ s ∈ Ioc (t0 - 1) taoUpperEdge := by
  filter_upwards [ae_taoCaseThreeTrialMeasure_mem] with s hs
  rcases hs with rfl | hs
  · exact Or.inl rfl
  · refine Or.inr ⟨?_, hs.2⟩
    have hleft : t0 - 1 < taoCaseThreeLeftA := by
      unfold taoCaseThreeCenterCeiling taoCaseThreeLeftA at *
      linarith
    exact hleft.trans_le hs.1

theorem taoCaseThreeTrialMeasure_singleton_on_rootInterval
    {t0 s : ℝ}
    (ht0Lower : taoCaseThreeCenterFloor ≤ t0)
    (ht0Upper : t0 ≤ taoCaseThreeCenterCeiling)
    (hs : s ∈ Icc (t0 - 1) (t0 + 1)) :
    taoCaseThreeTrialMeasure {s} = 0 := by
  apply taoCaseThreeTrialMeasure_singleton
  · have hleftPos : 0 < t0 - 1 := by
      unfold taoCaseThreeCenterFloor at ht0Lower
      norm_num at ht0Lower ⊢
      linarith
    exact ne_of_gt (hleftPos.trans_le hs.1)
  · have hsUpper : s < taoUpperEdge := by
      have hceiling : taoCaseThreeInputCeiling < taoUpperEdge :=
        tao_case_three_inputCeiling_lt_upperEdge
      unfold taoCaseThreeCenterCeiling taoCaseThreeInputCeiling at *
      linarith [hs.2]
    exact ne_of_lt hsUpper

end

end WangTrial

end

open MeasureTheory Set WangTrial

theorem OMA.solution : OMA.R_Erdos1038_erdos_1038_parts_ii_R1_H2_R1.H2 := by
  intro a ha ha₁
  let ν := taoCaseThreeTrialMeasure
  have hc : taoCaseThreeCenterFloor ≤ a + 1 := by
    unfold taoCaseThreeCenterFloor
    linarith
  have hd : a + 1 ≤ taoCaseThreeCenterCeiling := by
    unfold taoCaseThreeCenterCeiling
    linarith
  refine ⟨ν, inferInstanceAs (IsFiniteMeasure taoCaseThreeTrialMeasure), ?_, ?_, ?_⟩
  · intro he
    have hpos := taoCaseThreeTrialMeasure_potential_neg hc hd (a + 1)
      (show a + 1 ∈ Icc (a + 1 - 1) (a + 1 + 1) by constructor <;> linarith)
    change taoCaseThreeTrialMeasure = 0 at he
    simp [taoTrialMeasurePotential, he] at hpos
  · apply MeasureTheory.ae_iff.mp
    filter_upwards [ae_taoCaseThreeTrialMeasure_source_support hd] with s hs
    change s ∈ ({0} ∪ Icc a (2 * Real.sqrt 2) : Set ℝ)
    rcases hs with rfl | hs
    · exact Or.inl rfl
    · exact Or.inr ⟨by linarith [hs.1], hs.2⟩
  · intro t ht
    have ht' : t ∈ Icc (a + 1 - 1) (a + 1 + 1) := by constructor <;> linarith [ht.1, ht.2]
    refine ⟨taoCaseThreeTrialMeasure_singleton_on_rootInterval hc hd ht',
      integrable_log_sub_taoCaseThreeTrialMeasure t, ?_⟩
    have hneg := taoCaseThreeTrialMeasure_potential_neg hc hd t ht'
    change -(∫ s, Real.log |t - s| ∂ν) < 0 at hneg
    simp_rw [abs_sub_comm t] at hneg
    linarith
