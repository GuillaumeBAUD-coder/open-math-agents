import OMAReductions.R_Erdos297_erdos_297_variants_general_R1
import Mathlib

/-! The right endpoint Riemann sum is squeezed between the integral and the
integral plus one mesh width times the total variation. Calibration identifies
the entropy using the binary entropy identity for the logistic function. -/

open Filter Real MeasureTheory Erdos297
open scoped Topology

namespace E297

private noncomputable def w (l y : ℝ) := 1/(y*(1+exp (l/y)))

private lemma lambda_eq {x l : ℝ} (hx : 0 < x) (hl : massIntegral l = x) :
    lambdaOf x = l := by
  have uniq {u v : ℝ} (hu : massIntegral u = x) (hv : massIntegral v = x) (hlt : u < v) : False := by
    have iu : IntervalIntegrable (w u) volume 0 1 := intervalIntegral.intervalIntegrable_of_integral_ne_zero
      (show massIntegral u ≠ 0 by simpa [hu] using hx.ne')
    have iv : IntervalIntegrable (w v) volume 0 1 := intervalIntegral.intervalIntegrable_of_integral_ne_zero
      (show massIntegral v ≠ 0 by simpa [hv] using hx.ne')
    have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on (iu.sub iv) (by
      intro y hy
      have hy0 := hy.1
      apply sub_pos.mpr
      exact one_div_lt_one_div_of_lt (by positivity)
        (mul_lt_mul_of_pos_left (add_lt_add_right (exp_lt_exp.mpr (div_lt_div_of_pos_right hlt hy.1)) 1) hy.1))
      zero_lt_one
    rw [intervalIntegral.integral_sub iu iv] at hpos
    change 0 < massIntegral u - massIntegral v at hpos
    linarith
  have hs : {u : ℝ | massIntegral u = x} = {l} := by
    ext u
    change massIntegral u = x ↔ u = l
    constructor
    · intro hu
      exact le_antisymm (le_of_not_gt (uniq hl hu)) (le_of_not_gt (uniq hu hl))
    · rintro rfl
      exact hl
  rw [lambdaOf, hs, csInf_singleton]

private lemma calibration_pos {x l : ℝ} (hx : 0 < x) (hl : massIntegral l = x) : 0 < l := by
  have iw : IntervalIntegrable (w l) volume 0 1 := intervalIntegral.intervalIntegrable_of_integral_ne_zero
    (show massIntegral l ≠ 0 by simpa [hl] using hx.ne')
  by_contra! h
  have hi : IntervalIntegrable (fun y : ℝ => y⁻¹) volume 0 1 := by
    apply (iw.const_mul 2).mono_fun' (by fun_prop)
    rw [Set.uIoc_of_le zero_le_one]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hy0 := hy.1
    have he : exp (l/y) ≤ 1 := exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg h hy0.le)
    change ‖y⁻¹‖ ≤ 2*(1/(y*(1+exp (l/y))))
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy0)]
    field_simp
    linarith
  simpa [intervalIntegrable_inv_iff] using hi

private noncomputable def F (l y : ℝ) := if 0 < y then log (1+exp (-l/y)) else 0

private lemma F_mono {l : ℝ} (hl : 0 < l) : Monotone (F l) := by
  intro u v huv
  by_cases hu : 0 < u
  · have hv := hu.trans_le huv
    simp only [F, if_pos hu, if_pos hv]
    apply log_le_log (by positivity)
    apply add_le_add_right
    apply exp_le_exp.mpr
    rw [neg_div, neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_left hl.le hu huv)
  · simp only [F, if_neg hu]
    split_ifs
    · apply log_nonneg
      linarith [exp_pos (-l/v)]
    · rfl

private lemma riemann (g : ℝ → ℝ) (hg : Monotone g) :
    Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, g ((i+1 : ℕ)/(n : ℝ))) / n)
      atTop (𝓝 (∫ y in (0:ℝ)..1, g y)) := by
  let J := ∫ y in (0:ℝ)..1, g y
  have squeeze (n : ℕ) (hn : 0 < n) : J ≤ (∑ i ∈ Finset.range n, g ((i+1 : ℕ)/(n : ℝ))) / n ∧
      (∑ i ∈ Finset.range n, g ((i+1 : ℕ)/(n : ℝ))) / n ≤ J + (g 1-g 0)/n := by
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    let h (t : ℝ) := g (t/n)
    have mono : Monotone h := fun _ _ hxy => hg (div_le_div_of_nonneg_right hxy hn'.le)
    have lo := MonotoneOn.sum_le_integral (x₀ := (0:ℝ)) (a := n) (f := h) (mono.monotoneOn _)
    have hi := MonotoneOn.integral_le_sum (x₀ := (0:ℝ)) (a := n) (f := h) (mono.monotoneOn _)
    simp only [zero_add] at lo hi
    have I : (∫ y in (0:ℝ)..n, h y) = n*J := by
      simp [h, J, intervalIntegral.integral_comp_div g hn'.ne', hn'.ne']
    rw [I] at lo hi
    have e := Eq.trans (Finset.sum_range_succ' (fun i : ℕ => h i) n).symm (Finset.sum_range_succ (fun i : ℕ => h i) n)
    simp only [Nat.cast_zero] at e
    have h₀ : h 0 = g 0 := by simp [h]
    have h₁ : h n = g 1 := by simp [h,hn'.ne']
    rw [h₀,h₁] at e
    refine ⟨(le_div_iff₀ hn').mpr (by simpa [h,mul_comm] using hi), ?_⟩
    apply (div_le_iff₀ hn').mpr
    rw [add_mul, div_mul_cancel₀ _ hn'.ne']
    change (∑ i ∈ Finset.range n, h (i+1 : ℕ)) ≤ _
    linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => J)
    (h := fun n : ℕ => J + (g 1-g 0)/n) tendsto_const_nhds
  · simpa [div_eq_mul_inv] using tendsto_const_nhds.add ((tendsto_one_div_atTop_nhds_zero_nat).const_mul (g 1-g 0))
  · filter_upwards [eventually_gt_atTop 0] with n hn using (squeeze n hn).1
  · filter_upwards [eventually_gt_atTop 0] with n hn using (squeeze n hn).2


private lemma logistic_entropy (a : ℝ) :
    binEntropy (1/(1+exp a)) = a/(1+exp a) + log (1+exp (-a)) := by
  have he := exp_pos a
  have he' := exp_pos (-a)
  have hlog : log (1+exp a) = a + log (1+exp (-a)) := by
    calc
      _ = log (exp a*(1+exp (-a))) := by
        congr 1
        rw [exp_neg]
        field_simp
        <;> ring
      _ = _ := by rw [log_mul he.ne' (by positivity), log_exp]
  have hc : 1-1/(1+exp a) = 1/(1+exp (-a)) := by
    rw [exp_neg]
    field_simp
    ring
  rw [binEntropy, hc]
  simp only [one_div, inv_inv, hlog]
  rw [← one_div, ← one_div, ← hc]
  ring

end E297

open E297 in
theorem OMA.solution : OMA.R_Erdos297_erdos_297_variants_general_R1.H2 := by
  classical
  intro x l hx hm
  have hx' : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hl := calibration_pos hx' hm
  have hmono := F_mono hl
  have iw : IntervalIntegrable (w l) volume 0 1 :=
    intervalIntegral.intervalIntegrable_of_integral_ne_zero
      (show massIntegral l ≠ 0 by simpa [hm] using hx'.ne')
  have ig : IntervalIntegrable (F l) volume 0 1 := hmono.intervalIntegrable
  have ident : exponentOf x * log 2 = l*x + ∫ y in (0:ℝ)..1, F l y := by
    rw [exponentOf, lambda_eq hx' hm, intervalIntegral.integral_div,
      div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne']
    rw [← hm]
    change _ = l * (∫ y in (0:ℝ)..1, w l y) + _
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (iw.const_mul l) ig]
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le zero_le_one]
    filter_upwards with y hy
    have hy0 : 0 < y := hy.1
    rw [logistic_entropy, F, if_pos hy0, neg_div]
    dsimp [w]
    rw [mul_comm y, one_div, mul_inv_rev]
    ring
  rw [ident]
  apply (Tendsto.const_add ((l:ℝ)*x) (riemann (F l) hmono)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  congr 2
  rw [Real.log_prod (fun (p : ℕ) _ => (by positivity : (0 : ℝ) < 1 + exp (-l * N / (p : ℝ))).ne')]
  rw [show Finset.Icc 1 N = Finset.Ico 1 (N+1) by ext i; simp, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro i hi
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hir : (0:ℝ) < (i:ℝ)+1 := by positivity
  simp only [Nat.cast_succ, Nat.cast_add, Nat.cast_one, F, if_pos (div_pos hir hNr)]
  congr 3
  rw [div_div_eq_mul_div]
  ring
