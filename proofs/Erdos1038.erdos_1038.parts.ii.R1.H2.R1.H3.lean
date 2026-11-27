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

theorem sqrt_two_lt_three_halves : Real.sqrt 2 < 3 / 2 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [sqrt_two_sq]

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

def taoPointIntervalTrialPotential (A a b t : ℝ) : ℝ :=
  -Real.log |t| + A * (∫ s in a..b, -Real.log |t - s|)

theorem taoPointIntervalTrialPotential_eq
    (A a b t : ℝ) :
    taoPointIntervalTrialPotential A a b t =
      -Real.log |t| +
        A * (taoLogPrimitive (b - t) - taoLogPrimitive (a - t)) := by
  rw [taoPointIntervalTrialPotential, intervalDensityPotential_eq_primitive]

def taoCaseTwoFloor : ℝ := 7987 / 10000

def taoCaseTwoCenterFloor : ℝ := 17987 / 10000

def taoCaseTwoA : ℝ := 7233 / 10000

def taoCaseTwoLeftEndpoint : ℝ := 1134371 / 500000

def taoCaseTwoPotential (t : ℝ) : ℝ :=
  -Real.log t +
    taoCaseTwoA *
      (taoLogPrimitive (taoUpperEdge - t) -
        taoLogPrimitive (taoCaseTwoLeftEndpoint - t))

theorem tao_case_two_trial_eq_potential {t : ℝ} (ht : 0 < t) :
    taoPointIntervalTrialPotential taoCaseTwoA
        taoCaseTwoLeftEndpoint taoUpperEdge t =
      taoCaseTwoPotential t := by
  rw [taoPointIntervalTrialPotential_eq]
  simp only [abs_of_pos ht]
  rfl

theorem tao_case_two_center_interval_mem_floor
    {t0 t : ℝ} (ht0 : taoCaseTwoCenterFloor ≤ t0)
    (ht : t ∈ Icc (t0 - 1) (t0 + 1)) :
    taoCaseTwoFloor ≤ t := by
  unfold taoCaseTwoCenterFloor taoCaseTwoFloor at *
  linarith [ht.1]

end

end WangTrial

end

section
open Set

namespace WangTrial

noncomputable section

def taoCaseTwoPotentialDerivative (t : ℝ) : ℝ :=
  -1 / t + taoCaseTwoA *
    (Real.log |taoUpperEdge - t| -
      Real.log |taoCaseTwoLeftEndpoint - t|)

def taoCaseTwoPotentialSecondDerivative (t : ℝ) : ℝ :=
  1 / t ^ 2 + taoCaseTwoA *
    (-1 / (taoUpperEdge - t) +
      1 / (taoCaseTwoLeftEndpoint - t))

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

theorem hasDerivAt_taoCaseTwoPotential {t : ℝ}
    (ht : t ≠ 0)
    (hM : taoUpperEdge - t ≠ 0)
    (ha : taoCaseTwoLeftEndpoint - t ≠ 0) :
    HasDerivAt taoCaseTwoPotential
      (taoCaseTwoPotentialDerivative t) t := by
  have hzero : HasDerivAt (fun x : ℝ ↦ -Real.log x) (-1 / t) t := by
    convert! (Real.hasDerivAt_log ht).neg using 1
    ring
  have hinterval :=
    (hasDerivAt_taoLogPrimitive_const_sub hM).sub
      (hasDerivAt_taoLogPrimitive_const_sub ha)
  have hscaled := hinterval.const_mul taoCaseTwoA
  convert! hzero.add hscaled using 1

theorem hasDerivAt_taoCaseTwoPotentialDerivative {t : ℝ}
    (ht : t ≠ 0)
    (hM : taoUpperEdge - t ≠ 0)
    (ha : taoCaseTwoLeftEndpoint - t ≠ 0) :
    HasDerivAt taoCaseTwoPotentialDerivative
      (taoCaseTwoPotentialSecondDerivative t) t := by
  have hrecip : HasDerivAt (fun x : ℝ ↦ -1 / x) (1 / t ^ 2) t := by
    convert! (hasDerivAt_const t (-1 : ℝ)).div (hasDerivAt_id t) ht using 1
    simp only [id_eq]
    field_simp [ht]
    ring
  have hlogs := (hasDerivAt_log_abs_const_sub hM).sub
    (hasDerivAt_log_abs_const_sub ha)
  have hscaled := hlogs.const_mul taoCaseTwoA
  convert! hrecip.add hscaled using 1
  unfold taoCaseTwoPotentialSecondDerivative
  ring

theorem hasDerivAt_deriv_taoCaseTwoPotential {t : ℝ}
    (ht : t ≠ 0)
    (hM : taoUpperEdge - t ≠ 0)
    (ha : taoCaseTwoLeftEndpoint - t ≠ 0) :
    HasDerivAt (deriv taoCaseTwoPotential)
      (taoCaseTwoPotentialSecondDerivative t) t := by
  have htM : t ≠ taoUpperEdge := (sub_ne_zero.mp hM).symm
  have hta : t ≠ taoCaseTwoLeftEndpoint := (sub_ne_zero.mp ha).symm
  have heq : Filter.EventuallyEq (nhds t)
      (deriv taoCaseTwoPotential) taoCaseTwoPotentialDerivative := by
    filter_upwards [eventually_ne_nhds ht, eventually_ne_nhds htM,
      eventually_ne_nhds hta] with y hy0 hyM hya
    exact (hasDerivAt_taoCaseTwoPotential hy0
      (sub_ne_zero.mpr hyM.symm) (sub_ne_zero.mpr hya.symm)).deriv
  exact (hasDerivAt_taoCaseTwoPotentialDerivative ht hM ha).congr_of_eventuallyEq
    heq

theorem deriv2_taoCaseTwoPotential {t : ℝ}
    (ht : t ≠ 0)
    (hM : taoUpperEdge - t ≠ 0)
    (ha : taoCaseTwoLeftEndpoint - t ≠ 0) :
    deriv^[2] taoCaseTwoPotential t =
      taoCaseTwoPotentialSecondDerivative t := by
  rw [show deriv^[2] taoCaseTwoPotential t =
      deriv (deriv taoCaseTwoPotential) t by rfl]
  exact (hasDerivAt_deriv_taoCaseTwoPotential ht hM ha).deriv

theorem continuousOn_taoCaseTwoPotential_Ioi :
    ContinuousOn taoCaseTwoPotential (Ioi (0 : ℝ)) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have ht0 : t ≠ 0 := ht.ne'
  have hzero : ContinuousAt (fun x : ℝ ↦ -Real.log x) t :=
    (Real.continuousAt_log ht0).neg
  have hM : ContinuousAt
      (fun x : ℝ ↦ taoLogPrimitive (taoUpperEdge - x)) t :=
    continuous_taoLogPrimitive.continuousAt.comp
      (continuousAt_const.sub continuousAt_id)
  have ha : ContinuousAt
      (fun x : ℝ ↦ taoLogPrimitive (taoCaseTwoLeftEndpoint - x)) t :=
    continuous_taoLogPrimitive.continuousAt.comp
      (continuousAt_const.sub continuousAt_id)
  exact hzero.add ((hM.sub ha).const_mul taoCaseTwoA)

theorem tao_case_two_leftEndpoint_le_upperEdge :
    taoCaseTwoLeftEndpoint ≤ taoUpperEdge := by
  unfold taoCaseTwoLeftEndpoint taoUpperEdge
  nlinarith [seven_fifths_lt_sqrt_two]

theorem taoCaseTwoA_nonneg : 0 ≤ taoCaseTwoA := by
  norm_num [taoCaseTwoA]

theorem taoCaseTwoA_pos : 0 < taoCaseTwoA := by
  norm_num [taoCaseTwoA]

theorem tao_case_two_floor_pos : 0 < taoCaseTwoFloor := by
  norm_num [taoCaseTwoFloor]

theorem tao_case_two_floor_lt_leftEndpoint :
    taoCaseTwoFloor < taoCaseTwoLeftEndpoint := by
  norm_num [taoCaseTwoFloor, taoCaseTwoLeftEndpoint]

theorem tao_case_two_leftEndpoint_lt_upperEdge :
    taoCaseTwoLeftEndpoint < taoUpperEdge := by
  unfold taoCaseTwoLeftEndpoint taoUpperEdge
  nlinarith [seven_fifths_lt_sqrt_two]

theorem tao_case_two_upperEdge_sub_leftEndpoint_lt_one :
    taoUpperEdge - taoCaseTwoLeftEndpoint < 1 := by
  unfold taoUpperEdge taoCaseTwoLeftEndpoint
  nlinarith [sqrt_two_lt_three_halves]

theorem taoCaseTwoPotentialSecondDerivative_pos_of_left
    {t : ℝ} (ht : t ∈ Ioo taoCaseTwoFloor taoCaseTwoLeftEndpoint) :
    0 < taoCaseTwoPotentialSecondDerivative t := by
  have htPos : 0 < t := tao_case_two_floor_pos.trans ht.1
  have haPos : 0 < taoCaseTwoLeftEndpoint - t := sub_pos.mpr ht.2
  have hMPos : 0 < taoUpperEdge - t :=
    sub_pos.mpr (ht.2.trans tao_case_two_leftEndpoint_lt_upperEdge)
  have hInv :
      0 < -1 / (taoUpperEdge - t) +
        1 / (taoCaseTwoLeftEndpoint - t) := by
    have hden : taoCaseTwoLeftEndpoint - t < taoUpperEdge - t := by
      linarith [tao_case_two_leftEndpoint_lt_upperEdge]
    have hlt : 1 / (taoUpperEdge - t) <
        1 / (taoCaseTwoLeftEndpoint - t) :=
      one_div_lt_one_div_of_lt haPos hden
    rw [neg_div]
    linarith
  have hfirst : 0 < 1 / t ^ 2 :=
    div_pos zero_lt_one (sq_pos_of_pos htPos)
  have hsecond : 0 < taoCaseTwoA *
      (-1 / (taoUpperEdge - t) +
        1 / (taoCaseTwoLeftEndpoint - t)) :=
    mul_pos taoCaseTwoA_pos hInv
  unfold taoCaseTwoPotentialSecondDerivative
  linarith

theorem taoCaseTwoPotentialSecondDerivative_neg_of_middle
    {t : ℝ} (ht : t ∈ Ioo taoCaseTwoLeftEndpoint taoUpperEdge) :
    taoCaseTwoPotentialSecondDerivative t < 0 := by
  have haTwo : 2 < taoCaseTwoLeftEndpoint := by
    norm_num [taoCaseTwoLeftEndpoint]
  have htTwo : 2 < t := haTwo.trans ht.1
  have htSq : 4 < t ^ 2 := by nlinarith
  have hfirst : 1 / t ^ 2 < (1 / 4 : ℝ) :=
    one_div_lt_one_div_of_lt (by norm_num) htSq
  have huPos : 0 < t - taoCaseTwoLeftEndpoint := sub_pos.mpr ht.1
  have hvPos : 0 < taoUpperEdge - t := sub_pos.mpr ht.2
  have huOne : t - taoCaseTwoLeftEndpoint < 1 := by
    linarith [tao_case_two_upperEdge_sub_leftEndpoint_lt_one]
  have hvOne : taoUpperEdge - t < 1 := by
    linarith [tao_case_two_upperEdge_sub_leftEndpoint_lt_one]
  have hInvU : 1 < 1 / (t - taoCaseTwoLeftEndpoint) :=
    one_lt_one_div huPos huOne
  have hInvV : 1 < 1 / (taoUpperEdge - t) :=
    one_lt_one_div hvPos hvOne
  have hbracket :
      -1 / (taoUpperEdge - t) +
          1 / (taoCaseTwoLeftEndpoint - t) < -2 := by
    rw [show taoCaseTwoLeftEndpoint - t =
      -(t - taoCaseTwoLeftEndpoint) by ring,
      one_div_neg_eq_neg_one_div]
    rw [neg_div]
    linarith
  have hscaled := mul_lt_mul_of_pos_left hbracket taoCaseTwoA_pos
  have hASevenTenths : (7 / 10 : ℝ) < taoCaseTwoA := by
    norm_num [taoCaseTwoA]
  have hscaledBound : taoCaseTwoA *
      (-1 / (taoUpperEdge - t) +
        1 / (taoCaseTwoLeftEndpoint - t)) < -(7 / 5 : ℝ) := by
    calc
      taoCaseTwoA *
          (-1 / (taoUpperEdge - t) +
            1 / (taoCaseTwoLeftEndpoint - t)) <
          taoCaseTwoA * (-2) := hscaled
      _ < -(7 / 5 : ℝ) := by nlinarith
  unfold taoCaseTwoPotentialSecondDerivative
  linarith

theorem taoCaseTwoPotentialSecondDerivative_pos_of_right
    {t : ℝ} (ht : taoUpperEdge < t) :
    0 < taoCaseTwoPotentialSecondDerivative t := by
  have huPos : 0 < t - taoUpperEdge := sub_pos.mpr ht
  have hvPos : 0 < t - taoCaseTwoLeftEndpoint :=
    sub_pos.mpr (tao_case_two_leftEndpoint_lt_upperEdge.trans ht)
  have huv : t - taoUpperEdge < t - taoCaseTwoLeftEndpoint := by
    linarith [tao_case_two_leftEndpoint_lt_upperEdge]
  have hInv := one_div_lt_one_div_of_lt huPos huv
  have hbracket :
      0 < -1 / (taoUpperEdge - t) +
        1 / (taoCaseTwoLeftEndpoint - t) := by
    rw [show taoUpperEdge - t = -(t - taoUpperEdge) by ring,
      show taoCaseTwoLeftEndpoint - t =
        -(t - taoCaseTwoLeftEndpoint) by ring,
      neg_div_neg_eq, one_div_neg_eq_neg_one_div]
    linarith
  have htPos : 0 < t := by
    have hMPos : 0 < taoUpperEdge := by
      unfold taoUpperEdge
      positivity
    exact hMPos.trans ht
  have hfirst : 0 < 1 / t ^ 2 :=
    div_pos zero_lt_one (sq_pos_of_pos htPos)
  have hsecond := mul_pos taoCaseTwoA_pos hbracket
  unfold taoCaseTwoPotentialSecondDerivative
  linarith

theorem taoCaseTwoPotential_convexOn_left :
    ConvexOn ℝ (Icc taoCaseTwoFloor taoCaseTwoLeftEndpoint)
      taoCaseTwoPotential := by
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _)
  · exact continuousOn_taoCaseTwoPotential_Ioi.mono fun _ ht ↦
      tao_case_two_floor_pos.trans_le ht.1
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_taoCaseTwoPotential
      (tao_case_two_floor_pos.trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans tao_case_two_leftEndpoint_lt_upperEdge)).ne'
      (sub_pos.mpr ht.2).ne').differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_deriv_taoCaseTwoPotential
      (tao_case_two_floor_pos.trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans tao_case_two_leftEndpoint_lt_upperEdge)).ne'
      (sub_pos.mpr ht.2).ne').differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [deriv2_taoCaseTwoPotential
      (tao_case_two_floor_pos.trans ht.1).ne'
      (sub_pos.mpr (ht.2.trans tao_case_two_leftEndpoint_lt_upperEdge)).ne'
      (sub_pos.mpr ht.2).ne']
    exact (taoCaseTwoPotentialSecondDerivative_pos_of_left ht).le

theorem taoCaseTwoPotential_concaveOn_middle :
    ConcaveOn ℝ (Icc taoCaseTwoLeftEndpoint taoUpperEdge)
      taoCaseTwoPotential := by
  have haPos : 0 < taoCaseTwoLeftEndpoint := by
    norm_num [taoCaseTwoLeftEndpoint]
  apply concaveOn_of_deriv2_nonpos (convex_Icc _ _)
  · exact continuousOn_taoCaseTwoPotential_Ioi.mono fun _ ht ↦
      (by
        exact haPos.trans_le ht.1)
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_taoCaseTwoPotential
      (haPos.trans ht.1).ne'
      (sub_pos.mpr ht.2).ne'
      (sub_neg.mpr ht.1).ne).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_deriv_taoCaseTwoPotential
      (haPos.trans ht.1).ne'
      (sub_pos.mpr ht.2).ne'
      (sub_neg.mpr ht.1).ne).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [deriv2_taoCaseTwoPotential (haPos.trans ht.1).ne'
      (sub_pos.mpr ht.2).ne' (sub_neg.mpr ht.1).ne]
    exact (taoCaseTwoPotentialSecondDerivative_neg_of_middle ht).le

theorem taoCaseTwoPotential_convexOn_right :
    ConvexOn ℝ (Icc taoUpperEdge (taoUpperEdge + 1))
      taoCaseTwoPotential := by
  have hMPos : 0 < taoUpperEdge := by
    unfold taoUpperEdge
    positivity
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _)
  · exact continuousOn_taoCaseTwoPotential_Ioi.mono fun _ ht ↦ by
      exact hMPos.trans_le ht.1
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_taoCaseTwoPotential
      (hMPos.trans ht.1).ne'
      (sub_neg.mpr ht.1).ne
      (sub_neg.mpr (tao_case_two_leftEndpoint_lt_upperEdge.trans ht.1)).ne
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_deriv_taoCaseTwoPotential
      (hMPos.trans ht.1).ne'
      (sub_neg.mpr ht.1).ne
      (sub_neg.mpr (tao_case_two_leftEndpoint_lt_upperEdge.trans ht.1)).ne
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [deriv2_taoCaseTwoPotential (hMPos.trans ht.1).ne'
      (sub_neg.mpr ht.1).ne
      (sub_neg.mpr (tao_case_two_leftEndpoint_lt_upperEdge.trans ht.1)).ne]
    exact (taoCaseTwoPotentialSecondDerivative_pos_of_right ht.1).le

theorem taoCaseTwoPotential_neg_of_upperEdge_add_one_le
    {t : ℝ} (ht : taoUpperEdge + 1 ≤ t) :
    taoCaseTwoPotential t < 0 := by
  have htOne : 1 < t := by
    have hMPos : 0 < taoUpperEdge := by
      unfold taoUpperEdge
      positivity
    linarith
  have hlogt : -Real.log t < 0 := neg_lt_zero.mpr (Real.log_pos htOne)
  have hkernelNonneg :
      0 ≤ ∫ s in taoCaseTwoLeftEndpoint..taoUpperEdge,
        Real.log |t - s| := by
    apply intervalIntegral.integral_nonneg tao_case_two_leftEndpoint_le_upperEdge
    intro s hs
    have hdist : 1 ≤ t - s := by
      linarith [hs.2]
    rw [abs_of_nonneg (le_trans (by norm_num) hdist)]
    exact Real.log_nonneg hdist
  have hkernel :
      (∫ s in taoCaseTwoLeftEndpoint..taoUpperEdge,
          -Real.log |t - s|) ≤ 0 := by
    rw [intervalIntegral.integral_neg]
    linarith
  have hscaled :
      taoCaseTwoA *
          (∫ s in taoCaseTwoLeftEndpoint..taoUpperEdge,
            -Real.log |t - s|) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos taoCaseTwoA_nonneg hkernel
  rw [← tao_case_two_trial_eq_potential (lt_trans zero_lt_one htOne)]
  unfold taoPointIntervalTrialPotential
  rw [abs_of_pos (lt_trans zero_lt_one htOne)]
  linarith

theorem tao_case_two_of_compact_certificate
    (hcompact : ∀ t ∈ Icc taoCaseTwoFloor (taoUpperEdge + 1),
      taoCaseTwoPotential t < 0) :
    ∀ t, taoCaseTwoFloor ≤ t → taoCaseTwoPotential t < 0 := by
  intro t ht
  by_cases hupper : t ≤ taoUpperEdge + 1
  · exact hcompact t ⟨ht, hupper⟩
  · exact taoCaseTwoPotential_neg_of_upperEdge_add_one_le
      (le_of_not_ge hupper)

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

def evalTaoCaseTwoPotentialInterval
    (precision : Nat) (T : RatInterval) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let logT ← RatInterval.log? precision T
  let FM ← evalTaoLogPrimitiveInterval precision (RatInterval.sub M T)
  let Fa ← evalTaoLogPrimitiveInterval precision
    (RatInterval.sub (RatInterval.point (1134371 / 500000)) T)
  pure (RatInterval.add (RatInterval.neg logT)
    (RatInterval.mul (RatInterval.point (7233 / 10000))
      (RatInterval.sub FM Fa)))

theorem evalTaoCaseTwoPotentialInterval_contains
    {precision : Nat} {T R : RatInterval} {t : ℝ}
    (hT : T.Contains t)
    (hEval : evalTaoCaseTwoPotentialInterval precision T = some R) :
    R.Contains (taoCaseTwoPotential t) := by
  cases hS : RatInterval.sqrt? precision (RatInterval.point 2) with
  | none => simp [evalTaoCaseTwoPotentialInterval, hS] at hEval
  | some S =>
      let M := RatInterval.mul (RatInterval.point 2) S
      cases hlogT : RatInterval.log? precision T with
      | none =>
          simp [evalTaoCaseTwoPotentialInterval, hS, hlogT] at hEval
      | some logT =>
          cases hFM : evalTaoLogPrimitiveInterval precision
              (RatInterval.sub M T) with
          | none =>
              simp [evalTaoCaseTwoPotentialInterval, hS, hlogT,
                M, hFM] at hEval
          | some FM =>
              let XA := RatInterval.sub
                (RatInterval.point (1134371 / 500000)) T
              cases hFa : evalTaoLogPrimitiveInterval precision XA with
              | none =>
                  simp [evalTaoCaseTwoPotentialInterval, hS, hlogT,
                    XA, hFa] at hEval
              | some Fa =>
                  simp [evalTaoCaseTwoPotentialInterval, hS, hlogT,
                    M, hFM, XA, hFa] at hEval
                  subst R
                  have hTwo := RatInterval.point_contains (2 : Rat)
                  have hSContains := RatInterval.sqrt_contains
                    (RatInterval.point_contains (2 : Rat)) hS
                  have hM : M.Contains taoUpperEdge := by
                    simpa only [M, taoUpperEdge, Rat.cast_ofNat] using!
                      RatInterval.mul_contains hTwo hSContains
                  have hMT := RatInterval.sub_contains hM hT
                  have hFMContains := evalTaoLogPrimitiveInterval_contains
                    hMT hFM
                  have hARat := RatInterval.point_contains
                    (1134371 / 500000 : Rat)
                  have hAReal :
                      (RatInterval.point (1134371 / 500000)).Contains
                        taoCaseTwoLeftEndpoint := by
                    simpa only [taoCaseTwoLeftEndpoint, Rat.cast_div,
                      Rat.cast_ofNat] using! hARat
                  have hXA := RatInterval.sub_contains hAReal hT
                  have hFaContains := evalTaoLogPrimitiveInterval_contains
                    hXA hFa
                  have hlogContains := RatInterval.log_contains hT hlogT
                  have hWeightRat := RatInterval.point_contains
                    (7233 / 10000 : Rat)
                  have hWeight :
                      (RatInterval.point (7233 / 10000)).Contains
                        taoCaseTwoA := by
                    simpa only [taoCaseTwoA, Rat.cast_div,
                      Rat.cast_ofNat] using! hWeightRat
                  have hValue := RatInterval.add_contains
                    (RatInterval.neg_contains hlogContains)
                    (RatInterval.mul_contains hWeight
                      (RatInterval.sub_contains hFMContains hFaContains))
                  simpa only [taoCaseTwoPotential] using! hValue

def evalTaoCaseTwoDerivativeInterval
    (precision : Nat) (T : RatInterval) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let invT ← RatInterval.inv? T
  let absM ← RatInterval.abs? (RatInterval.sub M T)
  let logM ← RatInterval.log? precision absM
  let absA ← RatInterval.abs?
    (RatInterval.sub (RatInterval.point (1134371 / 500000)) T)
  let logA ← RatInterval.log? precision absA
  pure (RatInterval.add (RatInterval.neg invT)
    (RatInterval.mul (RatInterval.point (7233 / 10000))
      (RatInterval.sub logM logA)))

theorem evalTaoCaseTwoDerivativeInterval_contains
    {precision : Nat} {T R : RatInterval} {t : ℝ}
    (hT : T.Contains t)
    (hEval : evalTaoCaseTwoDerivativeInterval precision T = some R) :
    R.Contains (taoCaseTwoPotentialDerivative t) := by
  cases hS : RatInterval.sqrt? precision (RatInterval.point 2) with
  | none => simp [evalTaoCaseTwoDerivativeInterval, hS] at hEval
  | some S =>
      let M := RatInterval.mul (RatInterval.point 2) S
      cases hInvT : RatInterval.inv? T with
      | none =>
          simp [evalTaoCaseTwoDerivativeInterval, hS, hInvT] at hEval
      | some invT =>
          cases hAbsM : RatInterval.abs? (RatInterval.sub M T) with
          | none =>
              simp [evalTaoCaseTwoDerivativeInterval, hS, hInvT,
                M, hAbsM] at hEval
          | some absM =>
              cases hLogM : RatInterval.log? precision absM with
              | none =>
                  simp [evalTaoCaseTwoDerivativeInterval, hS, hInvT,
                    M, hAbsM, hLogM] at hEval
              | some logM =>
                  let XA := RatInterval.sub
                    (RatInterval.point (1134371 / 500000)) T
                  cases hAbsA : RatInterval.abs? XA with
                  | none =>
                      simp [evalTaoCaseTwoDerivativeInterval, hS, hInvT,
                        XA, hAbsA] at hEval
                  | some absA =>
                      cases hLogA : RatInterval.log? precision absA with
                      | none =>
                          simp [evalTaoCaseTwoDerivativeInterval, hS,
                            hInvT, XA, hAbsA,
                            hLogA] at hEval
                      | some logA =>
                          simp [evalTaoCaseTwoDerivativeInterval, hS,
                            hInvT, M, hAbsM, hLogM, XA, hAbsA,
                            hLogA] at hEval
                          subst R
                          have hTwo := RatInterval.point_contains (2 : Rat)
                          have hSContains := RatInterval.sqrt_contains
                            (RatInterval.point_contains (2 : Rat)) hS
                          have hM : M.Contains taoUpperEdge := by
                            simpa only [M, taoUpperEdge, Rat.cast_ofNat] using!
                              RatInterval.mul_contains hTwo hSContains
                          have hMT := RatInterval.sub_contains hM hT
                          have hAbsMContains :=
                            RatInterval.abs_contains hMT hAbsM
                          have hLogMContains := RatInterval.log_contains
                            hAbsMContains hLogM
                          have hARat := RatInterval.point_contains
                            (1134371 / 500000 : Rat)
                          have hAReal :
                              (RatInterval.point (1134371 / 500000)).Contains
                                taoCaseTwoLeftEndpoint := by
                            simpa only [taoCaseTwoLeftEndpoint, Rat.cast_div,
                              Rat.cast_ofNat] using! hARat
                          have hXA := RatInterval.sub_contains hAReal hT
                          have hAbsAContains :=
                            RatInterval.abs_contains hXA hAbsA
                          have hLogAContains := RatInterval.log_contains
                            hAbsAContains hLogA
                          have hInvContains :=
                            RatInterval.inv_contains hT hInvT
                          have hWeightRat := RatInterval.point_contains
                            (7233 / 10000 : Rat)
                          have hWeight :
                              (RatInterval.point (7233 / 10000)).Contains
                                taoCaseTwoA := by
                            simpa only [taoCaseTwoA, Rat.cast_div,
                              Rat.cast_ofNat] using! hWeightRat
                          have hValue := RatInterval.add_contains
                            (RatInterval.neg_contains hInvContains)
                            (RatInterval.mul_contains hWeight
                              (RatInterval.sub_contains hLogMContains
                                hLogAContains))
                          simpa only [taoCaseTwoPotentialDerivative,
                            neg_div, one_div, one_mul] using! hValue

theorem taoCaseTwoPotential_neg_of_interval_certificate
    {precision : Nat} {T : RatInterval} {t : ℝ}
    (hT : T.Contains t)
    (hcert : ∃ R, evalTaoCaseTwoPotentialInterval precision T = some R ∧
      R.hi < 0) :
    taoCaseTwoPotential t < 0 := by
  obtain ⟨R, hEval, hhi⟩ := hcert
  have hContains := evalTaoCaseTwoPotentialInterval_contains hT hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact hContains.2.trans_lt hhiReal

def evalTaoCaseTwoLeftTangentInterval
    (precision : Nat) (q : Rat) : Option RatInterval := do
  let P ← evalTaoCaseTwoPotentialInterval precision (RatInterval.point q)
  let D ← evalTaoCaseTwoDerivativeInterval precision (RatInterval.point q)
  pure (RatInterval.add P
    (RatInterval.mul D
      (RatInterval.point ((1134371 / 500000) - q))))

theorem evalTaoCaseTwoLeftTangentInterval_contains
    {precision : Nat} {q : Rat} {R : RatInterval}
    (hEval : evalTaoCaseTwoLeftTangentInterval precision q = some R) :
    R.Contains
      (taoCaseTwoPotential (q : ℝ) +
        taoCaseTwoPotentialDerivative (q : ℝ) *
          (taoCaseTwoLeftEndpoint - (q : ℝ))) := by
  cases hP : evalTaoCaseTwoPotentialInterval precision
      (RatInterval.point q) with
  | none => simp [evalTaoCaseTwoLeftTangentInterval, hP] at hEval
  | some P =>
      cases hD : evalTaoCaseTwoDerivativeInterval precision
          (RatInterval.point q) with
      | none =>
          simp [evalTaoCaseTwoLeftTangentInterval, hP, hD] at hEval
      | some D =>
          simp [evalTaoCaseTwoLeftTangentInterval, hP, hD] at hEval
          subst R
          have hQ := RatInterval.point_contains q
          have hPContains := evalTaoCaseTwoPotentialInterval_contains hQ hP
          have hDContains := evalTaoCaseTwoDerivativeInterval_contains hQ hD
          have hDeltaRat := RatInterval.point_contains
            ((1134371 / 500000 : Rat) - q)
          have hDelta :
              (RatInterval.point ((1134371 / 500000) - q)).Contains
                (taoCaseTwoLeftEndpoint - (q : ℝ)) := by
            simpa only [taoCaseTwoLeftEndpoint, Rat.cast_sub,
              Rat.cast_div, Rat.cast_ofNat] using! hDeltaRat
          exact RatInterval.add_contains hPContains
            (RatInterval.mul_contains hDContains hDelta)

def evalTaoCaseTwoPotentialAtLeftEndpoint
    (precision : Nat) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let A0 := RatInterval.point (1134371 / 500000)
  let logA ← RatInterval.log? precision A0
  let FM ← evalTaoLogPrimitiveInterval precision (RatInterval.sub M A0)
  pure (RatInterval.add (RatInterval.neg logA)
    (RatInterval.mul (RatInterval.point (7233 / 10000)) FM))

theorem evalTaoCaseTwoPotentialAtLeftEndpoint_contains
    {precision : Nat} {R : RatInterval}
    (hEval : evalTaoCaseTwoPotentialAtLeftEndpoint precision = some R) :
    R.Contains (taoCaseTwoPotential taoCaseTwoLeftEndpoint) := by
  cases hS : RatInterval.sqrt? precision (RatInterval.point 2) with
  | none => simp [evalTaoCaseTwoPotentialAtLeftEndpoint, hS] at hEval
  | some S =>
      let M := RatInterval.mul (RatInterval.point 2) S
      let A0 := RatInterval.point (1134371 / 500000)
      cases hlogA : RatInterval.log? precision A0 with
      | none =>
          simp [evalTaoCaseTwoPotentialAtLeftEndpoint, hS, A0,
            hlogA] at hEval
      | some logA =>
          cases hFM : evalTaoLogPrimitiveInterval precision
              (RatInterval.sub M A0) with
          | none =>
              simp [evalTaoCaseTwoPotentialAtLeftEndpoint, hS, M,
                A0, hlogA, hFM] at hEval
          | some FM =>
              simp [evalTaoCaseTwoPotentialAtLeftEndpoint, hS, M,
                A0, hlogA, hFM] at hEval
              subst R
              have hSContains := RatInterval.sqrt_contains
                (RatInterval.point_contains (2 : Rat)) hS
              have hM : M.Contains taoUpperEdge := by
                simpa only [M, taoUpperEdge, Rat.cast_ofNat] using!
                  RatInterval.mul_contains
                    (RatInterval.point_contains (2 : Rat)) hSContains
              have hARat := RatInterval.point_contains
                (1134371 / 500000 : Rat)
              have hA : A0.Contains taoCaseTwoLeftEndpoint := by
                simpa only [A0, taoCaseTwoLeftEndpoint, Rat.cast_div,
                  Rat.cast_ofNat] using! hARat
              have hlogContains := RatInterval.log_contains hA hlogA
              have hFMContains := evalTaoLogPrimitiveInterval_contains
                (RatInterval.sub_contains hM hA) hFM
              have hWeightRat := RatInterval.point_contains
                (7233 / 10000 : Rat)
              have hWeight :
                  (RatInterval.point (7233 / 10000)).Contains
                    taoCaseTwoA := by
                simpa only [taoCaseTwoA, Rat.cast_div,
                  Rat.cast_ofNat] using! hWeightRat
              have hValue := RatInterval.add_contains
                (RatInterval.neg_contains hlogContains)
                (RatInterval.mul_contains hWeight hFMContains)
              have hzero :
                  taoLogPrimitive
                    (taoCaseTwoLeftEndpoint - taoCaseTwoLeftEndpoint) = 0 := by
                rw [sub_self, taoLogPrimitive_zero]
              simpa only [taoCaseTwoPotential, hzero, sub_zero] using! hValue

def evalTaoCaseTwoPotentialAtUpperEdge
    (precision : Nat) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let logM ← RatInterval.log? precision M
  let Fa ← evalTaoLogPrimitiveInterval precision
    (RatInterval.sub (RatInterval.point (1134371 / 500000)) M)
  pure (RatInterval.sub (RatInterval.neg logM)
    (RatInterval.mul (RatInterval.point (7233 / 10000)) Fa))

theorem evalTaoCaseTwoPotentialAtUpperEdge_contains
    {precision : Nat} {R : RatInterval}
    (hEval : evalTaoCaseTwoPotentialAtUpperEdge precision = some R) :
    R.Contains (taoCaseTwoPotential taoUpperEdge) := by
  cases hS : RatInterval.sqrt? precision (RatInterval.point 2) with
  | none => simp [evalTaoCaseTwoPotentialAtUpperEdge, hS] at hEval
  | some S =>
      let M := RatInterval.mul (RatInterval.point 2) S
      cases hlogM : RatInterval.log? precision M with
      | none =>
          simp [evalTaoCaseTwoPotentialAtUpperEdge, hS, M,
            hlogM] at hEval
      | some logM =>
          let XA := RatInterval.sub
            (RatInterval.point (1134371 / 500000)) M
          cases hFa : evalTaoLogPrimitiveInterval precision XA with
          | none =>
              simp [evalTaoCaseTwoPotentialAtUpperEdge, hS, M,
                hlogM, XA, hFa] at hEval
          | some Fa =>
              simp [evalTaoCaseTwoPotentialAtUpperEdge, hS, M,
                hlogM, XA, hFa] at hEval
              subst R
              have hSContains := RatInterval.sqrt_contains
                (RatInterval.point_contains (2 : Rat)) hS
              have hM : M.Contains taoUpperEdge := by
                simpa only [M, taoUpperEdge, Rat.cast_ofNat] using!
                  RatInterval.mul_contains
                    (RatInterval.point_contains (2 : Rat)) hSContains
              have hlogContains := RatInterval.log_contains hM hlogM
              have hARat := RatInterval.point_contains
                (1134371 / 500000 : Rat)
              have hA :
                  (RatInterval.point (1134371 / 500000)).Contains
                    taoCaseTwoLeftEndpoint := by
                simpa only [taoCaseTwoLeftEndpoint, Rat.cast_div,
                  Rat.cast_ofNat] using! hARat
              have hFaContains := evalTaoLogPrimitiveInterval_contains
                (RatInterval.sub_contains hA hM) hFa
              have hWeightRat := RatInterval.point_contains
                (7233 / 10000 : Rat)
              have hWeight :
                  (RatInterval.point (7233 / 10000)).Contains
                    taoCaseTwoA := by
                simpa only [taoCaseTwoA, Rat.cast_div,
                  Rat.cast_ofNat] using! hWeightRat
              have hValue := RatInterval.sub_contains
                (RatInterval.neg_contains hlogContains)
                (RatInterval.mul_contains hWeight hFaContains)
              have hzero : taoLogPrimitive (taoUpperEdge - taoUpperEdge) = 0 := by
                rw [sub_self, taoLogPrimitive_zero]
              convert! hValue using 1
              unfold taoCaseTwoPotential
              rw [hzero]
              ring

end

end WangTrial

end

section
open Set

namespace WangTrial

noncomputable section

def taoCaseTwoTangentPointRat : Rat := 618079 / 250000

theorem taoCaseTwoTangentPoint_eq :
    (taoCaseTwoTangentPointRat : ℝ) = (2472316 / 1000000 : ℝ) := by
  norm_num [taoCaseTwoTangentPointRat]

set_option maxRecDepth 100000 in
theorem taoCaseTwo_floor_certificate :
    ∃ R, evalTaoCaseTwoPotentialInterval 50
        (RatInterval.point (7987 / 10000)) = some R ∧ R.hi < 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem taoCaseTwo_leftEndpoint_certificate :
    ∃ R, evalTaoCaseTwoPotentialAtLeftEndpoint 50 = some R ∧
      R.hi < 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem taoCaseTwo_upperEdge_certificate :
    ∃ R, evalTaoCaseTwoPotentialAtUpperEdge 50 = some R ∧
      R.hi < 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem taoCaseTwo_tangent_derivative_certificate :
    ∃ R, evalTaoCaseTwoDerivativeInterval 50
        (RatInterval.point taoCaseTwoTangentPointRat) = some R ∧
      R.hi < 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem taoCaseTwo_left_tangent_certificate :
    ∃ R, evalTaoCaseTwoLeftTangentInterval 50
        taoCaseTwoTangentPointRat = some R ∧ R.hi < 0 := by
  decide +kernel

theorem taoCaseTwoPotential_floor_neg :
    taoCaseTwoPotential taoCaseTwoFloor < 0 := by
  have hPoint := RatInterval.point_contains (7987 / 10000 : Rat)
  have hContains :
      (RatInterval.point (7987 / 10000)).Contains taoCaseTwoFloor := by
    simpa only [taoCaseTwoFloor, Rat.cast_div, Rat.cast_ofNat] using! hPoint
  exact taoCaseTwoPotential_neg_of_interval_certificate
    hContains taoCaseTwo_floor_certificate

theorem taoCaseTwoPotential_leftEndpoint_neg :
    taoCaseTwoPotential taoCaseTwoLeftEndpoint < 0 := by
  obtain ⟨R, hEval, hhi⟩ := taoCaseTwo_leftEndpoint_certificate
  have hContains := evalTaoCaseTwoPotentialAtLeftEndpoint_contains hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact hContains.2.trans_lt hhiReal

theorem taoCaseTwoPotential_upperEdge_neg :
    taoCaseTwoPotential taoUpperEdge < 0 := by
  obtain ⟨R, hEval, hhi⟩ := taoCaseTwo_upperEdge_certificate
  have hContains := evalTaoCaseTwoPotentialAtUpperEdge_contains hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact hContains.2.trans_lt hhiReal

theorem taoCaseTwoPotentialDerivative_tangentPoint_neg :
    taoCaseTwoPotentialDerivative (taoCaseTwoTangentPointRat : ℝ) < 0 := by
  obtain ⟨R, hEval, hhi⟩ := taoCaseTwo_tangent_derivative_certificate
  have hContains := evalTaoCaseTwoDerivativeInterval_contains
    (RatInterval.point_contains taoCaseTwoTangentPointRat) hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact hContains.2.trans_lt hhiReal

theorem taoCaseTwoPotential_leftTangent_neg :
    taoCaseTwoPotential (taoCaseTwoTangentPointRat : ℝ) +
        taoCaseTwoPotentialDerivative (taoCaseTwoTangentPointRat : ℝ) *
          (taoCaseTwoLeftEndpoint - (taoCaseTwoTangentPointRat : ℝ)) < 0 := by
  obtain ⟨R, hEval, hhi⟩ := taoCaseTwo_left_tangent_certificate
  have hContains := evalTaoCaseTwoLeftTangentInterval_contains hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact hContains.2.trans_lt hhiReal

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

theorem tao_case_two_tangentPoint_mem_middle :
    (taoCaseTwoTangentPointRat : ℝ) ∈
      Ioo taoCaseTwoLeftEndpoint taoUpperEdge := by
  constructor
  · norm_num [taoCaseTwoTangentPointRat, taoCaseTwoLeftEndpoint]
  · rw [taoCaseTwoTangentPoint_eq]
    unfold taoUpperEdge
    nlinarith [seven_fifths_lt_sqrt_two]

theorem taoCaseTwoPotential_neg_on_middle :
    ∀ t ∈ Icc taoCaseTwoLeftEndpoint taoUpperEdge,
      taoCaseTwoPotential t < 0 := by
  intro t ht
  let q : ℝ := taoCaseTwoTangentPointRat
  have hq : q ∈ Icc taoCaseTwoLeftEndpoint taoUpperEdge :=
    ⟨tao_case_two_tangentPoint_mem_middle.1.le,
      tao_case_two_tangentPoint_mem_middle.2.le⟩
  have hqPos : 0 < q := by
    exact (show 0 < taoCaseTwoLeftEndpoint by
      norm_num [taoCaseTwoLeftEndpoint]).trans
        tao_case_two_tangentPoint_mem_middle.1
  have hMne : taoUpperEdge - q ≠ 0 :=
    (sub_pos.mpr tao_case_two_tangentPoint_mem_middle.2).ne'
  have hane : taoCaseTwoLeftEndpoint - q ≠ 0 :=
    (sub_neg.mpr tao_case_two_tangentPoint_mem_middle.1).ne
  have hderiv : HasDerivAt taoCaseTwoPotential
      (taoCaseTwoPotentialDerivative q) q :=
    hasDerivAt_taoCaseTwoPotential hqPos.ne' hMne hane
  have htangent := ConcaveOn.le_tangent_of_hasDerivAt
    taoCaseTwoPotential_concaveOn_middle hq ht hderiv
  have hDneg : taoCaseTwoPotentialDerivative q < 0 := by
    simpa only [q] using! taoCaseTwoPotentialDerivative_tangentPoint_neg
  have hleftTangent :
      taoCaseTwoPotential q + taoCaseTwoPotentialDerivative q *
          (taoCaseTwoLeftEndpoint - q) < 0 := by
    simpa only [q] using! taoCaseTwoPotential_leftTangent_neg
  by_cases htq : t ≤ q
  · have hdelta : taoCaseTwoLeftEndpoint - q ≤ t - q := by
      linarith [ht.1]
    have hmul := mul_le_mul_of_nonpos_left hdelta hDneg.le
    exact htangent.trans_lt (by linarith)
  · have hqt : q < t := lt_of_not_ge htq
    have hmul : taoCaseTwoPotentialDerivative q * (t - q) < 0 :=
      mul_neg_of_neg_of_pos hDneg (sub_pos.mpr hqt)
    have hqNeg : taoCaseTwoPotential q < 0 := by
      have hleftDelta : taoCaseTwoLeftEndpoint - q < 0 :=
        sub_neg.mpr tao_case_two_tangentPoint_mem_middle.1
      have hleftProduct :
          0 < taoCaseTwoPotentialDerivative q *
            (taoCaseTwoLeftEndpoint - q) :=
        mul_pos_of_neg_of_neg hDneg hleftDelta
      linarith
    exact htangent.trans_lt (by linarith)

theorem taoCaseTwoPotential_neg_on_compact :
    ∀ t ∈ Icc taoCaseTwoFloor (taoUpperEdge + 1),
      taoCaseTwoPotential t < 0 := by
  intro t ht
  by_cases hta : t ≤ taoCaseTwoLeftEndpoint
  · have hle := taoCaseTwoPotential_convexOn_left.le_max_of_mem_Icc
      ⟨le_rfl, tao_case_two_floor_lt_leftEndpoint.le⟩
      ⟨tao_case_two_floor_lt_leftEndpoint.le, le_rfl⟩
      ⟨ht.1, hta⟩
    exact hle.trans_lt (max_lt taoCaseTwoPotential_floor_neg
      taoCaseTwoPotential_leftEndpoint_neg)
  · have hat : taoCaseTwoLeftEndpoint < t := lt_of_not_ge hta
    by_cases htM : t ≤ taoUpperEdge
    · exact taoCaseTwoPotential_neg_on_middle t ⟨hat.le, htM⟩
    · have hMt : taoUpperEdge < t := lt_of_not_ge htM
      have hle := taoCaseTwoPotential_convexOn_right.le_max_of_mem_Icc
        ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
        ⟨hMt.le, ht.2⟩
      have hrightNeg : taoCaseTwoPotential (taoUpperEdge + 1) < 0 :=
        taoCaseTwoPotential_neg_of_upperEdge_add_one_le le_rfl
      exact hle.trans_lt (max_lt taoCaseTwoPotential_upperEdge_neg hrightNeg)

theorem taoCaseTwoPotential_neg_of_floor_le :
    ∀ t, taoCaseTwoFloor ≤ t → taoCaseTwoPotential t < 0 :=
  tao_case_two_of_compact_certificate taoCaseTwoPotential_neg_on_compact

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

def taoCaseTwoTrialMeasure : Measure ℝ :=
  Measure.dirac 0 +
    taoIntervalTrialMeasure taoCaseTwoA taoCaseTwoLeftEndpoint taoUpperEdge

instance instIsFiniteMeasureTaoIntervalTrialMeasure (A a b : ℝ) :
    IsFiniteMeasure (taoIntervalTrialMeasure A a b) :=
  (volume.restrict (Icc a b)).smul_finite (by simp)

instance instIsFiniteMeasureTaoCaseTwoTrialMeasure :
    IsFiniteMeasure taoCaseTwoTrialMeasure := by
  unfold taoCaseTwoTrialMeasure
  infer_instance

theorem taoCaseTwoTrialMeasure_singleton {s : ℝ} (hs : s ≠ 0) :
    taoCaseTwoTrialMeasure {s} = 0 := by
  simp [taoCaseTwoTrialMeasure, hs, taoIntervalTrialMeasure]

theorem ae_taoIntervalTrialMeasure_mem (A a b : ℝ) :
    ∀ᵐ s ∂taoIntervalTrialMeasure A a b, s ∈ Icc a b := by
  exact Measure.ae_smul_measure
    (ae_restrict_mem measurableSet_Icc) _

theorem ae_taoCaseTwoTrialMeasure_mem :
    ∀ᵐ s ∂taoCaseTwoTrialMeasure,
      s = 0 ∨ s ∈ Icc taoCaseTwoLeftEndpoint taoUpperEdge := by
  rw [taoCaseTwoTrialMeasure, ae_add_measure_iff]
  constructor
  · simp
  · exact (ae_taoIntervalTrialMeasure_mem taoCaseTwoA
      taoCaseTwoLeftEndpoint taoUpperEdge).mono
        (fun s hs ↦ Or.inr hs)

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

theorem taoCaseTwoA_nonnegative : 0 ≤ taoCaseTwoA := by
  norm_num [taoCaseTwoA]

theorem integrable_log_t_sub_taoCaseTwoTrialMeasure (t : ℝ) :
    Integrable (fun x : ℝ ↦ Real.log |t - x|)
      taoCaseTwoTrialMeasure := by
  unfold taoCaseTwoTrialMeasure
  apply Integrable.add_measure
  · apply integrable_dirac
    finiteness
  · exact integrable_log_t_sub_taoIntervalTrialMeasure
      tao_case_two_leftEndpoint_le_upperEdge

theorem integrable_log_sub_taoCaseTwoTrialMeasure (r : ℝ) :
    Integrable (fun x : ℝ ↦ Real.log |x - r|)
      taoCaseTwoTrialMeasure := by
  refine (integrable_log_t_sub_taoCaseTwoTrialMeasure r).congr ?_
  filter_upwards [] with x
  rw [abs_sub_comm]

theorem taoCaseTwoTrialMeasure_potential {t : ℝ} (ht : 0 < t) :
    taoTrialMeasurePotential taoCaseTwoTrialMeasure t =
      taoCaseTwoPotential t := by
  have hdirac : Integrable (fun x : ℝ ↦ Real.log |t - x|)
      (Measure.dirac 0) := integrable_dirac (by finiteness)
  have hinterval := integrable_log_t_sub_taoIntervalTrialMeasure
    (A := taoCaseTwoA) (t := t) tao_case_two_leftEndpoint_le_upperEdge
  rw [taoCaseTwoTrialMeasure,
    taoTrialMeasurePotential_add hdirac hinterval,
    taoTrialMeasurePotential_dirac,
    taoTrialMeasurePotential_interval taoCaseTwoA_nonnegative
      tao_case_two_leftEndpoint_le_upperEdge]
  rw [sub_zero, abs_of_pos ht]
  rw [intervalDensityPotential_eq_primitive]
  rfl

end

end WangTrial

end

section
open MeasureTheory Set

namespace WangTrial

noncomputable section

theorem taoCaseTwoTrialMeasure_potential_neg
    {t0 : ℝ} (ht0 : taoCaseTwoCenterFloor ≤ t0) :
    ∀ t ∈ Icc (t0 - 1) (t0 + 1),
      taoTrialMeasurePotential taoCaseTwoTrialMeasure t < 0 := by
  intro t ht
  have hfloor := tao_case_two_center_interval_mem_floor ht0 ht
  have htPos : 0 < t := by
    unfold taoCaseTwoFloor at hfloor
    norm_num at hfloor ⊢
    linarith
  rw [taoCaseTwoTrialMeasure_potential htPos]
  exact taoCaseTwoPotential_neg_of_floor_le t hfloor

theorem ae_taoCaseTwoTrialMeasure_source_support
    {t0 : ℝ} (ht0Upper : t0 ≤ taoUpperEdge) :
    ∀ᵐ s ∂taoCaseTwoTrialMeasure,
      s = 0 ∨ s ∈ Ioc (t0 - 1) taoUpperEdge := by
  filter_upwards [ae_taoCaseTwoTrialMeasure_mem] with s hs
  rcases hs with rfl | hs
  · exact Or.inl rfl
  · refine Or.inr ⟨?_, hs.2⟩
    have hgap : taoUpperEdge < taoCaseTwoLeftEndpoint + 1 := by
      linarith [tao_case_two_upperEdge_sub_leftEndpoint_lt_one]
    linarith [hs.1, ht0Upper, hgap]

end

end WangTrial

end

open MeasureTheory Set WangTrial

theorem OMA.solution : OMA.R_Erdos1038_erdos_1038_parts_ii_R1_H2_R1.H3 := by
  intro a ha ha₁
  let ν := taoCaseTwoTrialMeasure
  have hc : taoCaseTwoCenterFloor ≤ a + 1 := by
    unfold taoCaseTwoCenterFloor
    linarith
  have hM : a + 1 ≤ taoUpperEdge := by
    unfold taoUpperEdge
    have := Real.one_le_sqrt.mpr (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  refine ⟨ν, inferInstanceAs (IsFiniteMeasure taoCaseTwoTrialMeasure), ?_, ?_, ?_⟩
  · intro he
    have hpos := taoCaseTwoTrialMeasure_potential_neg hc (a + 1)
      (show a + 1 ∈ Icc (a + 1 - 1) (a + 1 + 1) by constructor <;> linarith)
    change taoCaseTwoTrialMeasure = 0 at he
    simp [taoTrialMeasurePotential, he] at hpos
  · apply MeasureTheory.ae_iff.mp
    filter_upwards [ae_taoCaseTwoTrialMeasure_source_support hM] with s hs
    change s ∈ ({0} ∪ Icc a (2 * Real.sqrt 2) : Set ℝ)
    rcases hs with rfl | hs
    · exact Or.inl rfl
    · exact Or.inr ⟨by linarith [hs.1], hs.2⟩
  · intro t ht
    have ht0 : t ≠ 0 := by have := ht.1; linarith
    refine ⟨taoCaseTwoTrialMeasure_singleton ht0, integrable_log_sub_taoCaseTwoTrialMeasure t, ?_⟩
    have hneg := taoCaseTwoTrialMeasure_potential_neg hc t
      (show t ∈ Icc (a + 1 - 1) (a + 1 + 1) by constructor <;> linarith [ht.1, ht.2])
    change -(∫ s, Real.log |t - s| ∂ν) < 0 at hneg
    simp_rw [abs_sub_comm t] at hneg
    linarith
