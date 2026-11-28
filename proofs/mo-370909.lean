import OMAStatements.S_mo_370909
import Mathlib

open OMA.S_mo_370909 MeasureTheory

lemma pointwise (t p : ℝ) (ht : 0 ≤ t) (hp : 1 < p) :
    t * Real.log t ≤ 2 * |t - 1| + 2 / (p - 1) * |t - 1| ^ p := by
  have hs : 0 < p - 1 := by linarith
  have hR : 0 ≤ 2 / (p - 1) * |t - 1| ^ p := by positivity
  rcases le_or_gt t 1 with h1 | h1
  · have : t * Real.log t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht (Real.log_nonpos ht h1)
    have : 0 ≤ 2 * |t - 1| := by positivity
    linarith
  · set x := t - 1 with hx
    have hx0 : 0 < x := by linarith
    have habs : |t - 1| = x := abs_of_pos hx0
    rw [habs]
    have ht' : t = 1 + x := by linarith
    rcases le_or_gt x 1 with hx1 | hx1
    · have hlog : Real.log t ≤ x := by
        have := Real.log_le_sub_one_of_pos (by linarith : 0 < t); linarith
      have hlog0 : 0 ≤ Real.log t := Real.log_nonneg h1.le
      have h1' : t * Real.log t ≤ t * x := mul_le_mul_of_nonneg_left hlog ht
      have h2' : 0 ≤ 2 / (p - 1) * x ^ p := by positivity
      have h3' : t * x ≤ 2 * x := by rw [ht']; nlinarith
      linarith
    · -- t ≤ 2x, log t ≤ log 2 + log x, log x ≤ x^(p-1)/(p-1)
      have ht2 : t ≤ 2 * x := by linarith
      have hlogt : Real.log t ≤ Real.log (2 * x) := Real.log_le_log (by linarith) ht2
      have hlog2x : Real.log (2 * x) = Real.log 2 + Real.log x :=
        Real.log_mul (by norm_num) hx0.ne'
      have hl2 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
      have hlx : Real.log x ≤ x ^ (p - 1) / (p - 1) := Real.log_le_rpow_div hx0.le hs
      have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg h1.le
      have hxp : x ^ p = x * x ^ (p - 1) := by
        rw [← Real.rpow_one_add' hx0.le (by linarith)]; congr 1; ring
      have key : t * Real.log t ≤ 2 * x * (Real.log 2 + Real.log x) := by
        rw [← hlog2x]
        exact mul_le_mul ht2 hlogt hlogt0 (by linarith)
      have key2 : 2 * x * (Real.log 2 + Real.log x) ≤ 2 * x + 2 / (p - 1) * x ^ p := by
        rw [hxp]
        have : 2 * x * Real.log x ≤ 2 * x * (x ^ (p - 1) / (p - 1)) :=
          mul_le_mul_of_nonneg_left hlx (by linarith)
        have : 2 * x * Real.log 2 ≤ 2 * x := by nlinarith
        have e : 2 * x * (x ^ (p - 1) / (p - 1)) = 2 / (p - 1) * (x * x ^ (p - 1)) := by
          field_simp
        nlinarith
      linarith

theorem OMA.solution : type_of% @OMA.S_mo_370909.main := by
  intro Ω _ μ _ f p hp hfm hf0 hf1 hint
  have hfi : Integrable f μ := by
    by_contra h
    rw [integral_undef h] at hf1
    norm_num at hf1
  have hgi : Integrable (fun x => |f x - 1|) μ := (hfi.sub (integrable_const 1)).abs
  have hIp : 0 ≤ ∫ x, |f x - 1| ^ p ∂μ :=
    integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  have hI1 : 0 ≤ ∫ x, |f x - 1| ∂μ := integral_nonneg (fun x => abs_nonneg _)
  have hJ : (∫ x, |f x - 1| ∂μ) ^ p ≤ ∫ x, |f x - 1| ^ p ∂μ :=
    (convexOn_rpow hp.le).map_integral_le
      ((Real.continuous_rpow_const (by linarith : 0 ≤ p)).continuousOn) isClosed_Ici
      (ae_of_all _ (fun x => Set.mem_Ici.mpr (abs_nonneg _))) hgi hint
  have hL1 : ∫ x, |f x - 1| ∂μ ≤ (∫ x, |f x - 1| ^ p ∂μ) ^ (1 / p) := by
    calc ∫ x, |f x - 1| ∂μ = ((∫ x, |f x - 1| ∂μ) ^ p) ^ (1 / p) := by
          rw [one_div, Real.rpow_rpow_inv hI1 (by linarith)]
      _ ≤ (∫ x, |f x - 1| ^ p ∂μ) ^ (1 / p) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hI1 _) hJ (by positivity)
  have hRnn : 0 ≤ 2 * (∫ x, |f x - 1| ^ p ∂μ) ^ (1 / p) + 2 / (p - 1) * ∫ x, |f x - 1| ^ p ∂μ := by
    have hs : 0 < p - 1 := by linarith
    have := Real.rpow_nonneg hIp (1 / p)
    positivity
  by_cases hfl : Integrable (fun x => f x * Real.log (f x)) μ
  · have hb : Integrable (fun x => 2 * |f x - 1| + 2 / (p - 1) * |f x - 1| ^ p) μ :=
      (hgi.const_mul 2).add (hint.const_mul _)
    calc ∫ x, f x * Real.log (f x) ∂μ
        ≤ ∫ x, (2 * |f x - 1| + 2 / (p - 1) * |f x - 1| ^ p) ∂μ :=
          integral_mono hfl hb (fun x => pointwise (f x) p (hf0 x) hp)
      _ = 2 * ∫ x, |f x - 1| ∂μ + 2 / (p - 1) * ∫ x, |f x - 1| ^ p ∂μ := by
          rw [integral_add (hgi.const_mul 2) (hint.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := by linarith
  · rw [integral_undef hfl]
    exact hRnn
