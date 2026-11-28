import FormalConjectures.ErdosProblems.«1043»

-- Problem: Erdős Problem 1043 — weak
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1043.lean:71 (declaration Erdos1043.erdos_1043.variants.weak)
-- Credit: @Jakeybakeypants (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

section Erdos1043WeakProof

open MeasureTheory Polynomial Set Filter

-- ============================================================================
-- Section 1: Elementary real, trigonometric, and log-integral inequalities
-- ============================================================================

private lemma log_one_add_ge_rat {t : ℝ} (ht : 0 ≤ t) :
    2 * t / (2 + t) ≤ Real.log (1 + t) := by
  let g : ℝ → ℝ := fun x => Real.log (1 + x) - 2 * x / (2 + x)
  have hg_mono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · refine ContinuousOn.sub ?_ ?_
      · refine (continuous_const.add continuous_id).continuousOn.log ?_
        intro x hx
        have hx0 : 0 ≤ x := mem_Ici.mp hx
        change 1 + x ≠ 0
        linarith
      · refine (continuous_const.mul continuous_id).continuousOn.div
          (continuous_const.add continuous_id).continuousOn ?_
        intro x hx
        have hx0 : 0 ≤ x := mem_Ici.mp hx
        change 2 + x ≠ 0
        linarith
    · intro x hx
      have hx' : 0 < x := by simpa [interior_Ici] using hx
      have h1 : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + x)) x := by
        simpa using ((hasDerivAt_id x).const_add 1).log (by change 1 + x ≠ 0; linarith)
      have h2 : HasDerivAt (fun y => 2 * y / (2 + y)) (4 / (2 + x) ^ 2) x := by
        have hd := ((hasDerivAt_id x).const_mul 2).div ((hasDerivAt_id x).const_add 2)
          (by change 2 + x ≠ 0; linarith)
        simp only [id_eq] at hd
        refine hd.congr_deriv ?_
        have hx2 : 2 + x ≠ 0 := by linarith
        field_simp
        ring
      exact (h1.sub h2).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : 0 < x := by simpa [interior_Ici] using hx
      have h1 : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + x)) x := by
        simpa using ((hasDerivAt_id x).const_add 1).log (by change 1 + x ≠ 0; linarith)
      have h2 : HasDerivAt (fun y => 2 * y / (2 + y)) (4 / (2 + x) ^ 2) x := by
        have hd := ((hasDerivAt_id x).const_mul 2).div ((hasDerivAt_id x).const_add 2)
          (by change 2 + x ≠ 0; linarith)
        simp only [id_eq] at hd
        refine hd.congr_deriv ?_
        have hx2 : 2 + x ≠ 0 := by linarith
        field_simp
        ring
      have hg : HasDerivAt g (1 / (1 + x) - 4 / (2 + x) ^ 2) x := h1.sub h2
      rw [hg.deriv]
      have hx1 : 1 + x ≠ 0 := by linarith
      have hx2 : 2 + x ≠ 0 := by linarith
      have hd : 1 / (1 + x) - 4 / (2 + x) ^ 2 = x ^ 2 / ((1 + x) * (2 + x) ^ 2) := by
        field_simp
        ring
      rw [hd]
      positivity
  have hle := hg_mono (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  simp only [g, add_zero, Real.log_one, mul_zero, zero_div, sub_zero] at hle
  linarith

private lemma half_log_one_add_sq_ge (r : ℝ) :
    r ^ 2 / (2 + r ^ 2) ≤ (1 / 2 : ℝ) * Real.log (1 + r ^ 2) := by
  have h := log_one_add_ge_rat (sq_nonneg r)
  have h2 : 2 * r ^ 2 / (2 + r ^ 2) = 2 * (r ^ 2 / (2 + r ^ 2)) := by ring
  rw [h2] at h
  linarith

private lemma half_log_amgm_ge {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((a - b) / (a + b)) ^ 2 ≤ (1 / 2 : ℝ) * Real.log ((a ^ 2 + b ^ 2) / (2 * a * b)) := by
  have ht : 0 ≤ (a - b) ^ 2 / (2 * a * b) := by positivity
  have h := log_one_add_ge_rat ht
  have hid1 : 1 + (a - b) ^ 2 / (2 * a * b) = (a ^ 2 + b ^ 2) / (2 * a * b) := by
    field_simp
    ring
  have hid2 : 2 * ((a - b) ^ 2 / (2 * a * b)) / (2 + (a - b) ^ 2 / (2 * a * b)) =
      2 * ((a - b) / (a + b)) ^ 2 := by
    field_simp
    ring
  rw [hid1, hid2] at h
  linarith

private lemma nonneg_of_deriv_nonneg {u v : ℝ → ℝ} (hu : Continuous u)
    (hdv : ∀ t, HasDerivAt u (v t) t) (hu0 : u 0 = 0)
    (hvpos : ∀ t ≥ 0, v t ≥ 0) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ u t := by
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici 0) hu.continuousOn
    (fun y _ => (hdv y).differentiableAt.differentiableWithinAt)
    (fun y hy => by rw [(hdv y).deriv]; exact hvpos y (le_of_lt (by simpa [interior_Ici] using hy)))
  simpa [hu0] using hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht

private lemma sin_taylor5_bound {x : ℝ} (hx : 0 ≤ x) :
    |Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120)| ≤ x ^ 7 / 5040 := by
  have h1l : ∀ t ≥ 0, 0 ≤ Real.sin t + t := fun t ht =>
    nonneg_of_deriv_nonneg (Real.continuous_sin.add continuous_id)
      (fun y => (Real.hasDerivAt_sin y).add (hasDerivAt_id y))
      (by simp) (fun y _ => by linarith [Real.neg_one_le_cos y]) ht
  have h1u : ∀ t ≥ 0, 0 ≤ t - Real.sin t := fun t ht =>
    nonneg_of_deriv_nonneg (continuous_id.sub Real.continuous_sin)
      (fun y => (hasDerivAt_id y).sub (Real.hasDerivAt_sin y))
      (by simp) (fun y _ => by linarith [Real.cos_le_one y]) ht
  have h2l : ∀ t ≥ 0, 0 ≤ Real.cos t - (1 - t ^ 2 / 2) := fun t ht =>
    nonneg_of_deriv_nonneg
      (Real.continuous_cos.sub (continuous_const.sub ((continuous_pow 2).div_const 2)))
      (fun y => ((Real.hasDerivAt_cos y).sub
        ((hasDerivAt_const y 1).sub ((hasDerivAt_pow 2 y).div_const 2))).congr_deriv (by ring))
      (by simp) h1u ht
  have h2u : ∀ t ≥ 0, 0 ≤ (1 + t ^ 2 / 2) - Real.cos t := fun t ht =>
    nonneg_of_deriv_nonneg
      ((continuous_const.add ((continuous_pow 2).div_const 2)).sub Real.continuous_cos)
      (fun y => (((hasDerivAt_const y 1).add
        ((hasDerivAt_pow 2 y).div_const 2)).sub (Real.hasDerivAt_cos y)).congr_deriv (by ring))
      (by simp) h1l ht
  have h3l : ∀ t ≥ 0, 0 ≤ Real.sin t - (t - t ^ 3 / 6) := fun t ht =>
    nonneg_of_deriv_nonneg
      (Real.continuous_sin.sub (continuous_id.sub ((continuous_pow 3).div_const 6)))
      (fun y => ((Real.hasDerivAt_sin y).sub
        ((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 6))).congr_deriv (by ring))
      (by simp) h2l ht
  have h4u : ∀ t ≥ 0, 0 ≤ (1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t := fun t ht =>
    nonneg_of_deriv_nonneg
      (((continuous_const.sub ((continuous_pow 2).div_const 2)).add
        ((continuous_pow 4).div_const 24)).sub Real.continuous_cos)
      (fun y => ((((hasDerivAt_const y 1).sub ((hasDerivAt_pow 2 y).div_const 2)).add
        ((hasDerivAt_pow 4 y).div_const 24)).sub (Real.hasDerivAt_cos y)).congr_deriv (by ring))
      (by simp) h3l ht
  have h5u : ∀ t ≥ 0, 0 ≤ (t - t ^ 3 / 6 + t ^ 5 / 120) - Real.sin t := fun t ht =>
    nonneg_of_deriv_nonneg
      (((continuous_id.sub ((continuous_pow 3).div_const 6)).add
        ((continuous_pow 5).div_const 120)).sub Real.continuous_sin)
      (fun y => ((((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 6)).add
        ((hasDerivAt_pow 5 y).div_const 120)).sub (Real.hasDerivAt_sin y)).congr_deriv (by ring))
      (by simp) h4u ht
  have h6l : ∀ t ≥ 0, 0 ≤ Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) := fun t ht =>
    nonneg_of_deriv_nonneg
      (Real.continuous_cos.sub (((continuous_const.sub ((continuous_pow 2).div_const 2)).add
        ((continuous_pow 4).div_const 24)).sub ((continuous_pow 6).div_const 720)))
      (fun y => ((Real.hasDerivAt_cos y).sub
        ((((hasDerivAt_const y 1).sub ((hasDerivAt_pow 2 y).div_const 2)).add
          ((hasDerivAt_pow 4 y).div_const 24)).sub
          ((hasDerivAt_pow 6 y).div_const 720))).congr_deriv (by ring))
      (by simp) h5u ht
  have h7l : ∀ t ≥ 0, 0 ≤ Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040) := fun t ht =>
    nonneg_of_deriv_nonneg
      (Real.continuous_sin.sub (((continuous_id.sub ((continuous_pow 3).div_const 6)).add
        ((continuous_pow 5).div_const 120)).sub ((continuous_pow 7).div_const 5040)))
      (fun y => ((Real.hasDerivAt_sin y).sub
        ((((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 6)).add
          ((hasDerivAt_pow 5 y).div_const 120)).sub
          ((hasDerivAt_pow 7 y).div_const 5040))).congr_deriv (by ring))
      (by simp) h6l ht
  have hlo := h7l x hx
  have hhi := h5u x hx
  rw [abs_le]
  constructor <;> linarith [pow_nonneg hx 7]

noncomputable def alphaFn (t : ℝ) : ℝ := (1 - Real.cos (Real.pi * t)) / 2

private lemma alphaFn_eq_sin_sq (t : ℝ) :
    alphaFn t = Real.sin (Real.pi * t / 2) ^ 2 := by
  unfold alphaFn
  have h1 := Real.cos_two_mul (Real.pi * t / 2)
  have h2 := Real.sin_sq_add_cos_sq (Real.pi * t / 2)
  have h3 : 2 * (Real.pi * t / 2) = Real.pi * t := by ring
  rw [h3] at h1
  linarith

private lemma alphaFn_mem_Icc (t : ℝ) : alphaFn t ∈ Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · rw [alphaFn_eq_sin_sq]; exact sq_nonneg _
  · unfold alphaFn; linarith [Real.neg_one_le_cos (Real.pi * t)]

private lemma alphaFn_strictMonoOn : StrictMonoOn alphaFn (Icc (0 : ℝ) 1) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  unfold alphaFn
  have hcos : Real.cos (Real.pi * t₂) < Real.cos (Real.pi * t₁) := by
    apply Real.strictAntiOn_cos
    · exact ⟨mul_nonneg Real.pi_pos.le ht₁.1, mul_le_of_le_one_right Real.pi_pos.le ht₁.2⟩
    · exact ⟨mul_nonneg Real.pi_pos.le ht₂.1, mul_le_of_le_one_right Real.pi_pos.le ht₂.2⟩
    · exact mul_lt_mul_of_pos_left hlt Real.pi_pos
  linarith

private lemma alphaFn_symm (t : ℝ) : alphaFn (1 - t) = 1 - alphaFn t := by
  unfold alphaFn
  rw [mul_sub, mul_one, Real.cos_pi_sub]
  ring

private lemma alphaFn_rat_bounds_box (q lo hi : ℚ) (hq0 : 0 ≤ q)
    (hlo : (((((3.1415 : ℚ) * q / 2) - ((3.1416 : ℚ) * q / 2) ^ 3 / 6 +
        ((3.1415 : ℚ) * q / 2) ^ 5 / 120 - ((3.1416 : ℚ) * q / 2) ^ 7 / 5040) ^ 2) ≥ lo))
    (hhi : (((((3.1416 : ℚ) * q / 2) - ((3.1415 : ℚ) * q / 2) ^ 3 / 6 +
        ((3.1416 : ℚ) * q / 2) ^ 5 / 120 + ((3.1416 : ℚ) * q / 2) ^ 7 / 5040) ^ 2) ≤ hi))
    (hpos : 0 ≤ (3.1415 : ℚ) * q / 2 - ((3.1416 : ℚ) * q / 2) ^ 3 / 6 +
        ((3.1415 : ℚ) * q / 2) ^ 5 / 120 - ((3.1416 : ℚ) * q / 2) ^ 7 / 5040) :
    (lo : ℝ) ≤ alphaFn q ∧ alphaFn q ≤ (hi : ℝ) := by
  rw [alphaFn_eq_sin_sq]
  let x : ℝ := Real.pi * (q : ℝ) / 2
  let xlo : ℝ := ((3.1415 : ℚ) * q / 2 : ℚ)
  let xhi : ℝ := ((3.1416 : ℚ) * q / 2 : ℚ)
  have hq0r : (0 : ℝ) ≤ q := by exact_mod_cast hq0
  have hxlo0 : 0 ≤ xlo := by dsimp [xlo]; push_cast; positivity
  have hxlo_le : xlo ≤ x := by
    dsimp [xlo, x]; push_cast; have := Real.pi_gt_d4; nlinarith
  have hxhi_le : x ≤ xhi := by
    dsimp [xhi, x]; push_cast; have := Real.pi_lt_d4; nlinarith
  have hx0 : 0 ≤ x := le_trans hxlo0 hxlo_le
  have hxhi0 : 0 ≤ xhi := le_trans hx0 hxhi_le
  have hpow3 : x ^ 3 ≤ xhi ^ 3 := pow_le_pow_left₀ hx0 hxhi_le 3
  have hpow3_lo : xlo ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hxlo0 hxlo_le 3
  have hpow5_lo : xlo ^ 5 ≤ x ^ 5 := pow_le_pow_left₀ hxlo0 hxlo_le 5
  have hpow5_hi : x ^ 5 ≤ xhi ^ 5 := pow_le_pow_left₀ hx0 hxhi_le 5
  have hpow7 : x ^ 7 ≤ xhi ^ 7 := pow_le_pow_left₀ hx0 hxhi_le 7
  have hbd := sin_taylor5_bound hx0
  rw [abs_le] at hbd
  have hpos_r : 0 ≤ xlo - xhi ^ 3 / 6 + xlo ^ 5 / 120 - xhi ^ 7 / 5040 := by
    dsimp [xlo, xhi]; exact_mod_cast hpos
  have h_s_lo : xlo - xhi ^ 3 / 6 + xlo ^ 5 / 120 - xhi ^ 7 / 5040 ≤ Real.sin x := by linarith [hbd.1]
  have h_s_hi : Real.sin x ≤ xhi - xlo ^ 3 / 6 + xhi ^ 5 / 120 + xhi ^ 7 / 5040 := by linarith [hbd.2]
  have hsq_lo : (xlo - xhi ^ 3 / 6 + xlo ^ 5 / 120 - xhi ^ 7 / 5040) ^ 2 ≤ Real.sin x ^ 2 :=
    pow_le_pow_left₀ hpos_r h_s_lo 2
  have hsq_hi : Real.sin x ^ 2 ≤ (xhi - xlo ^ 3 / 6 + xhi ^ 5 / 120 + xhi ^ 7 / 5040) ^ 2 :=
    pow_le_pow_left₀ (le_trans hpos_r h_s_lo) h_s_hi 2
  have hlo_r : (lo : ℝ) ≤ (xlo - xhi ^ 3 / 6 + xlo ^ 5 / 120 - xhi ^ 7 / 5040) ^ 2 := by
    dsimp [xlo, xhi]; exact_mod_cast hlo
  have hhi_r : (xhi - xlo ^ 3 / 6 + xhi ^ 5 / 120 + xhi ^ 7 / 5040) ^ 2 ≤ (hi : ℝ) := by
    dsimp [xlo, xhi]; exact_mod_cast hhi
  exact ⟨le_trans hlo_r hsq_lo, le_trans hsq_hi hhi_r⟩

private lemma alphaFn_bound_1 :
    (846 / 10000 : ℝ) ≤ alphaFn (188 / 1000 : ℚ) ∧ alphaFn (188 / 1000 : ℚ) ≤ 848 / 10000 := by
  simpa using alphaFn_rat_bounds_box (188 / 1000) (846 / 10000) (848 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private lemma alphaFn_bound_2 :
    (1657 / 10000 : ℝ) ≤ alphaFn (267 / 1000 : ℚ) ∧ alphaFn (267 / 1000 : ℚ) ≤ 1659 / 10000 := by
  simpa using alphaFn_rat_bounds_box (267 / 1000) (1657 / 10000) (1659 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private lemma alphaFn_bound_3 :
    (2440 / 10000 : ℝ) ≤ alphaFn (329 / 1000 : ℚ) ∧ alphaFn (329 / 1000 : ℚ) ≤ 2442 / 10000 := by
  simpa using alphaFn_rat_bounds_box (329 / 1000) (2440 / 10000) (2442 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private lemma alphaFn_bound_4 :
    (3188 / 10000 : ℝ) ≤ alphaFn (382 / 1000 : ℚ) ∧ alphaFn (382 / 1000 : ℚ) ≤ 3190 / 10000 := by
  simpa using alphaFn_rat_bounds_box (382 / 1000) (3188 / 10000) (3190 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private lemma alphaFn_bound_5 :
    (3893 / 10000 : ℝ) ≤ alphaFn (429 / 1000 : ℚ) ∧ alphaFn (429 / 1000 : ℚ) ≤ 3895 / 10000 := by
  simpa using alphaFn_rat_bounds_box (429 / 1000) (3893 / 10000) (3895 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private lemma alphaFn_bound_6 :
    (4513 / 10000 : ℝ) ≤ alphaFn (469 / 1000 : ℚ) ∧ alphaFn (469 / 1000 : ℚ) ≤ 4515 / 10000 := by
  simpa using alphaFn_rat_bounds_box (469 / 1000) (4513 / 10000) (4515 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private lemma integral_log_abs_alpha_sub {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    IntegrableOn (fun t => Real.log |alphaFn t - c|) (Ioo 0 1) volume ∧
    (∫ t in Ioo (0 : ℝ) 1, Real.log |alphaFn t - c|) = -2 * Real.log 2 := by
  let s : ℝ := Real.arccos (1 - 2 * c) / Real.pi
  have hc_cos : 1 - 2 * c ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hc.2], by linarith [hc.1]⟩
  have hs_mem : s ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le,
      (div_le_one Real.pi_pos).mpr (Real.arccos_le_pi _)⟩
  have hcs : alphaFn s = c := by
    unfold alphaFn
    rw [show Real.pi * s = Real.arccos (1 - 2 * c) by dsimp [s]; field_simp [Real.pi_ne_zero],
      Real.cos_arccos hc_cos.1 hc_cos.2]
    ring
  have hdiff : ∀ t : ℝ, alphaFn t - c =
      Real.sin (Real.pi * (t + s) / 2) * Real.sin (Real.pi * (t - s) / 2) := by
    intro t
    rw [← hcs]
    unfold alphaFn
    have hsub := Real.cos_sub_cos (Real.pi * t) (Real.pi * s)
    have ha : (Real.pi * t + Real.pi * s) / 2 = Real.pi * (t + s) / 2 := by ring
    have hb : (Real.pi * t - Real.pi * s) / 2 = Real.pi * (t - s) / 2 := by ring
    rw [ha, hb] at hsub
    linarith
  have hsplit_ae : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Real.log |alphaFn t - c| =
        Real.log (Real.sin (Real.pi * (t + s) / 2)) +
        Real.log (Real.sin (Real.pi * (t - s) / 2)) := by
    have hnull : ({s} : Set ℝ)ᶜ ∈ ae (volume.restrict (Ioo (0 : ℝ) 1)) := by
      rw [mem_ae_iff, compl_compl, Measure.restrict_apply₀ (NullMeasurableSet.of_null (measure_singleton s))]
      exact measure_mono_null inter_subset_left (measure_singleton s)
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hnull] with t ht hne
    have hts_ne : t ≠ s := by simpa using hne
    rw [hdiff t, abs_mul, Real.log_mul]
    · rw [Real.log_abs, Real.log_abs]
    · rw [abs_ne_zero]
      apply Real.sin_ne_zero_iff.mpr
      intro k hk
      have h1 : 0 < Real.pi * (t + s) / 2 := by nlinarith [Real.pi_pos, ht.1, hs_mem.1]
      have h2 : Real.pi * (t + s) / 2 < Real.pi := by nlinarith [Real.pi_pos, ht.2, hs_mem.2]
      rcases le_or_gt k 0 with hk0 | hk1
      · have : (k : ℝ) * Real.pi ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hk0) Real.pi_pos.le
        linarith
      · have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
        have : Real.pi ≤ (k : ℝ) * Real.pi := le_mul_of_one_le_left Real.pi_pos.le this
        linarith
    · rw [abs_ne_zero]
      apply Real.sin_ne_zero_iff.mpr
      intro k hk
      have h1 : -(Real.pi / 2) < Real.pi * (t - s) / 2 := by nlinarith [Real.pi_pos, ht.1, hs_mem.2]
      have h2 : Real.pi * (t - s) / 2 < Real.pi / 2 := by nlinarith [Real.pi_pos, ht.2, hs_mem.1]
      have hk0 : k = 0 := by
        by_contra hk0
        rcases lt_or_gt_of_ne hk0 with hkn | hkp
        · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hkn
          have : (k : ℝ) * Real.pi ≤ -Real.pi := by nlinarith [Real.pi_pos]
          linarith [Real.pi_pos]
        · have : (1 : ℝ) ≤ k := by exact_mod_cast hkp
          have : Real.pi ≤ (k : ℝ) * Real.pi := le_mul_of_one_le_left Real.pi_pos.le this
          linarith [Real.pi_pos]
      subst hk0
      simp only [Int.cast_zero, zero_mul] at hk
      have : t - s = 0 := by
        have := div_eq_zero_iff.mp hk.symm
        rcases this with h0 | h0
        · exact (mul_eq_zero.mp h0).resolve_left Real.pi_ne_zero
        · norm_num at h0
      exact hts_ne (sub_eq_zero.mp this)
  have hpne : (Real.pi / 2 : ℝ) ≠ 0 := by positivity
  have hint1 : IntervalIntegrable (fun t => Real.log (Real.sin (Real.pi * (t + s) / 2))) volume 0 1 := by
    have hadd : IntervalIntegrable (fun u => (Real.log ∘ Real.sin) (u + Real.pi * s / 2)) volume 0 (Real.pi / 2) := by
      have hbase := intervalIntegrable_log_sin (a := Real.pi * s / 2) (b := Real.pi / 2 + Real.pi * s / 2)
      simpa using hbase.comp_add_right (Real.pi * s / 2)
    have hmul : IntervalIntegrable (fun t => (Real.log ∘ Real.sin) (Real.pi / 2 * t + Real.pi * s / 2)) volume 0 1 := by
      simpa [div_self hpne] using hadd.comp_mul_left (c := Real.pi / 2)
    refine hmul.congr_ae ?_
    filter_upwards with t
    simp only [Function.comp_apply]
    congr 2; ring
  have hint2 : IntervalIntegrable (fun t => Real.log (Real.sin (Real.pi * (t - s) / 2))) volume 0 1 := by
    have hadd : IntervalIntegrable (fun u => (Real.log ∘ Real.sin) (u + (-Real.pi * s / 2))) volume 0 (Real.pi / 2) := by
      have hbase := intervalIntegrable_log_sin (a := -Real.pi * s / 2) (b := Real.pi / 2 + (-Real.pi * s / 2))
      simpa using hbase.comp_add_right (-Real.pi * s / 2)
    have hmul : IntervalIntegrable (fun t => (Real.log ∘ Real.sin) (Real.pi / 2 * t + (-Real.pi * s / 2))) volume 0 1 := by
      simpa [div_self hpne] using hadd.comp_mul_left (c := Real.pi / 2)
    refine hmul.congr_ae ?_
    filter_upwards with t
    simp only [Function.comp_apply]
    congr 2; ring
  have hint_sum : IntervalIntegrable
      (fun t => Real.log (Real.sin (Real.pi * (t + s) / 2)) +
                Real.log (Real.sin (Real.pi * (t - s) / 2))) volume 0 1 := hint1.add hint2
  have hint_Ioo_sum : IntegrableOn
      (fun t => Real.log (Real.sin (Real.pi * (t + s) / 2)) +
                Real.log (Real.sin (Real.pi * (t - s) / 2))) (Ioo 0 1) volume :=
    hint_sum.1.mono_set Ioo_subset_Ioc_self
  have hint_Ioo : IntegrableOn (fun t => Real.log |alphaFn t - c|) (Ioo 0 1) volume :=
    hint_Ioo_sum.congr_fun_ae (Filter.EventuallyEq.symm hsplit_ae)
  refine ⟨hint_Ioo, ?_⟩
  calc ∫ t in Ioo (0 : ℝ) 1, Real.log |alphaFn t - c|
      = ∫ t in Ioo (0 : ℝ) 1, (Real.log (Real.sin (Real.pi * (t + s) / 2)) +
          Real.log (Real.sin (Real.pi * (t - s) / 2))) := integral_congr_ae hsplit_ae
    _ = ∫ t in (0 : ℝ)..1, (Real.log (Real.sin (Real.pi * (t + s) / 2)) +
          Real.log (Real.sin (Real.pi * (t - s) / 2))) := by
        rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
    _ = (∫ t in (0 : ℝ)..1, Real.log (Real.sin (Real.pi * (t + s) / 2))) +
        (∫ t in (0 : ℝ)..1, Real.log (Real.sin (Real.pi * (t - s) / 2))) :=
        intervalIntegral.integral_add hint1 hint2
    _ = (Real.pi / 2)⁻¹ * (∫ u in (Real.pi * s / 2)..(Real.pi * (1 + s) / 2), Real.log (Real.sin u)) +
        (Real.pi / 2)⁻¹ * (∫ u in (-Real.pi * s / 2)..(Real.pi * (1 - s) / 2), Real.log (Real.sin u)) := by
        congr 1
        · have h1 := intervalIntegral.integral_comp_mul_add (fun u => Real.log (Real.sin u)) hpne (Real.pi * s / 2) (a := (0 : ℝ)) (b := 1)
          simp only [mul_zero, zero_add, mul_one, smul_eq_mul] at h1
          rw [show Real.pi / 2 + Real.pi * s / 2 = Real.pi * (1 + s) / 2 by ring] at h1
          convert h1 using 2
          ext t; congr 2; ring
        · have h2 := intervalIntegral.integral_comp_mul_add (fun u => Real.log (Real.sin u)) hpne (-Real.pi * s / 2) (a := (0 : ℝ)) (b := 1)
          simp only [mul_zero, zero_add, mul_one, smul_eq_mul] at h2
          rw [show Real.pi / 2 + -Real.pi * s / 2 = Real.pi * (1 - s) / 2 by ring] at h2
          convert h2 using 2
          ext t; congr 2; ring
    _ = (Real.pi / 2)⁻¹ * ((∫ u in (Real.pi * s / 2)..(Real.pi * (1 + s) / 2), Real.log (Real.sin u)) +
          ((∫ u in (0 : ℝ)..(Real.pi * s / 2), Real.log (Real.sin u)) +
           (∫ u in (Real.pi * (1 + s) / 2)..Real.pi, Real.log (Real.sin u)))) := by
        rw [← mul_add]; congr 1; congr 1
        have hs1 : ∫ u in (-Real.pi * s / 2)..(Real.pi * (1 - s) / 2), Real.log (Real.sin u) =
            (∫ u in (-Real.pi * s / 2)..0, Real.log (Real.sin u)) +
            (∫ u in (0 : ℝ)..(Real.pi * (1 - s) / 2), Real.log (Real.sin u)) :=
          (intervalIntegral.integral_add_adjacent_intervals intervalIntegrable_log_sin intervalIntegrable_log_sin).symm
        rw [hs1]; congr 1
        · have hneg := intervalIntegral.integral_comp_neg (fun u => Real.log (Real.sin u)) (a := -Real.pi * s / 2) (b := 0)
          simp only [neg_zero] at hneg
          rw [show -(-Real.pi * s / 2) = Real.pi * s / 2 by ring] at hneg
          rw [← hneg]
          refine intervalIntegral.integral_congr (fun u _ => ?_)
          rw [Real.sin_neg, ← Real.log_abs (-Real.sin u), abs_neg, Real.log_abs]
        · have hpi := intervalIntegral.integral_comp_sub_left (fun u => Real.log (Real.sin u)) Real.pi (a := Real.pi * (1 + s) / 2) (b := Real.pi)
          rw [sub_self, show Real.pi - Real.pi * (1 + s) / 2 = Real.pi * (1 - s) / 2 by ring] at hpi
          rw [← hpi]
          refine intervalIntegral.integral_congr (fun u _ => ?_)
          rw [Real.sin_pi_sub]
    _ = (Real.pi / 2)⁻¹ * (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u)) := by
        congr 1
        have ha := intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_log_sin (a := 0) (b := Real.pi * s / 2))
          (intervalIntegrable_log_sin (a := Real.pi * s / 2) (b := Real.pi * (1 + s) / 2))
        have hb := intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_log_sin (a := 0) (b := Real.pi * (1 + s) / 2))
          (intervalIntegrable_log_sin (a := Real.pi * (1 + s) / 2) (b := Real.pi))
        dsimp only [Function.comp_def] at ha hb
        linarith
    _ = -2 * Real.log 2 := by
        rw [integral_log_sin_zero_pi]
        field_simp [Real.pi_ne_zero]

-- ============================================================================
-- Section 2: Compactness and Vandermonde capacity bound on levelSet f
-- ============================================================================

private lemma isCompact_levelSet {f : ℂ[X]} (hf : f.Monic) (hd : 1 ≤ f.degree) :
    IsCompact (Erdos1043.levelSet f) := by
  have hclosed : IsClosed (Erdos1043.levelSet f) :=
    isClosed_le f.continuous.norm continuous_const
  have hdeg0 : 0 < f.degree := lt_of_lt_of_le (by norm_num) hd
  have htend : Tendsto (fun z : ℂ => ‖f.eval z‖) (comap (norm : ℂ → ℝ) atTop) atTop :=
    f.tendsto_norm_atTop hdeg0 tendsto_comap
  have hev : ∀ᶠ z in comap (norm : ℂ → ℝ) atTop, (1 : ℝ) < ‖f.eval z‖ :=
    htend (Filter.Ioi_mem_atTop 1)
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp (Filter.eventually_comap.mp hev)
  have hsub : Erdos1043.levelSet f ⊆ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hlt
    push Not at hlt
    have hgt1 : 1 < ‖f.eval z‖ := hR (‖z‖) hlt.le z rfl
    exact absurd hz (not_le_of_gt hgt1)
  exact Metric.isCompact_of_isClosed_isBounded hclosed
    ((Metric.isBounded_iff_subset_closedBall 0).mpr ⟨R, hsub⟩)

private lemma factorial_le_pow (n : ℕ) : Nat.factorial n ≤ n ^ n := by
  induction n with
  | zero => simp
  | succ k hk =>
    rw [Nat.factorial_succ]
    calc (k + 1) * Nat.factorial k
        ≤ (k + 1) * k ^ k := Nat.mul_le_mul_left _ hk
      _ ≤ (k + 1) * (k + 1) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ k) k)
      _ = (k + 1) ^ (k + 1) := by rw [pow_succ']

private lemma vandermonde_log_bound {f : ℂ[X]} (hf : f.Monic) (hd : 1 ≤ f.degree) :
    ∃ M : ℝ, 1 ≤ M ∧ (∀ z ∈ Erdos1043.levelSet f, ‖z‖ ≤ M) ∧
      ∀ (n : ℕ), 2 ≤ n → ∀ (z : Fin n → ℂ), (∀ i, z i ∈ Erdos1043.levelSet f) →
        Function.Injective z →
        ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Real.log ‖z j - z i‖ ≤
          (n : ℝ) * Real.log (n : ℝ) + (f.natDegree : ℝ) * (n : ℝ) * Real.log M := by
  have hc := isCompact_levelSet hf hd
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hc.isBounded
  let M : ℝ := max 1 R
  have hM1 : 1 ≤ M := le_max_left 1 R
  have hzM : ∀ w ∈ Erdos1043.levelSet f, ‖w‖ ≤ M := fun w hw => by
    have := mem_closedBall_zero_iff.mp (hR hw)
    exact le_trans this (le_max_right 1 R)
  refine ⟨M, hM1, hzM, fun n _hn z hzK hinj => ?_⟩
  let d : ℕ := f.natDegree
  have hd_pos : 0 < d := by
    rw [Polynomial.degree_eq_natDegree hf.ne_zero] at hd
    exact_mod_cast hd
  let p : Fin n → ℂ[X] := fun j => X ^ ((j : ℕ) % d) * f ^ ((j : ℕ) / d)
  have hp_deg : ∀ j : Fin n, (p j).natDegree = (j : ℕ) := fun j => by
    dsimp [p]
    have hmod_ne : (X ^ ((j : ℕ) % d) : ℂ[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
    have hpow_monic : (f ^ ((j : ℕ) / d)).Monic := hf.pow _
    rw [Polynomial.natDegree_mul hmod_ne hpow_monic.ne_zero, Polynomial.natDegree_X_pow,
      hf.natDegree_pow, Nat.mul_comm ((j : ℕ) / d) d]
    exact Nat.mod_add_div j d
  have hp_monic : ∀ j : Fin n, (p j).Monic := fun j =>
    (monic_X_pow ((j : ℕ) % d)).mul (hf.pow _)
  have hp_bd : ∀ i j : Fin n, ‖(p j).eval (z i)‖ ≤ M ^ d := fun i j => by
    dsimp [p]
    rw [eval_mul, eval_pow, eval_X, eval_pow, norm_mul, norm_pow, norm_pow]
    have hfi : ‖f.eval (z i)‖ ≤ 1 := hzK i
    have hzi : ‖z i‖ ≤ M := hzM (z i) (hzK i)
    have hp1 : ‖f.eval (z i)‖ ^ ((j : ℕ) / d) ≤ 1 := pow_le_one₀ (norm_nonneg _) hfi
    have hp2 : ‖z i‖ ^ ((j : ℕ) % d) ≤ M ^ ((j : ℕ) % d) := pow_le_pow_left₀ (norm_nonneg _) hzi _
    have hp3 : M ^ ((j : ℕ) % d) ≤ M ^ d :=
      pow_le_pow_right₀ hM1 (le_of_lt (Nat.mod_lt _ hd_pos))
    calc ‖z i‖ ^ ((j : ℕ) % d) * ‖f.eval (z i)‖ ^ ((j : ℕ) / d)
        ≤ M ^ d * 1 := mul_le_mul (le_trans hp2 hp3) hp1 (pow_nonneg (norm_nonneg _) _) (pow_nonneg (by linarith) _)
      _ = M ^ d := mul_one _
  have hdet := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde z p hp_deg hp_monic
  have hdet_norm : ‖(Matrix.vandermonde z).det‖ ≤ (n.factorial : ℝ) * (M ^ d) ^ n := by
    rw [hdet, Matrix.det_apply]
    calc ‖∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i : Fin n, (p i).eval (z (σ i))‖
        ≤ ∑ σ : Equiv.Perm (Fin n), ‖Equiv.Perm.sign σ • ∏ i : Fin n, (p i).eval (z (σ i))‖ := norm_sum_le _ _
      _ = ∑ σ : Equiv.Perm (Fin n), ‖∏ i : Fin n, (p i).eval (z (σ i))‖ := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), (M ^ d) ^ n := by
          refine Finset.sum_le_sum fun σ _ => ?_
          rw [norm_prod]
          calc ∏ i : Fin n, ‖(p i).eval (z (σ i))‖
              ≤ ∏ _i : Fin n, M ^ d := Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hp_bd (σ i) i)
            _ = (M ^ d) ^ n := by simp
      _ = (n.factorial : ℝ) * (M ^ d) ^ n := by simp [Fintype.card_perm, Fintype.card_fin]
  have hdet_pos : 0 < ‖(Matrix.vandermonde z).det‖ := by
    rw [norm_pos_iff]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hlog := Real.log_le_log hdet_pos hdet_norm
  rw [Matrix.det_vandermonde, norm_prod] at hlog
  simp_rw [norm_prod] at hlog
  have hprod_ne : ∀ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖z j - z i‖ ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.mpr fun j hj => norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun heq =>
      ne_of_lt (Finset.mem_Ioi.mp hj) (hinj heq).symm)
  have hlog_lhs : Real.log (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖z j - z i‖) =
      ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Real.log ‖z j - z i‖ := by
    rw [Real.log_prod (fun i _ => hprod_ne i)]
    refine Finset.sum_congr rfl fun i _ => Real.log_prod (fun j hj => norm_ne_zero_iff.mpr
      (sub_ne_zero.mpr fun heq => ne_of_lt (Finset.mem_Ioi.mp hj) (hinj heq).symm))
  have hfact_pos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hM_pos : 0 < M := by linarith
  have hlog_rhs : Real.log ((n.factorial : ℝ) * (M ^ d) ^ n) ≤
      (n : ℝ) * Real.log (n : ℝ) + (d : ℝ) * (n : ℝ) * Real.log M := by
    rw [Real.log_mul hfact_pos.ne' (pow_ne_zero _ (pow_ne_zero _ hM_pos.ne')), Real.log_pow, Real.log_pow]
    have hf_le : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast factorial_le_pow n
    have hlf : Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
      simpa [Real.log_pow] using Real.log_le_log hfact_pos hf_le
    linarith [show (n : ℝ) * ((d : ℝ) * Real.log M) = (d : ℝ) * (n : ℝ) * Real.log M by ring]
  exact le_trans (hlog_lhs ▸ hlog) hlog_rhs

-- ============================================================================
-- Section 3: Orthogonal projection volume = volume (re '' K) / volume (im '' K)
-- ============================================================================

private noncomputable def lineEquiv (u : ℂ) (hu : ‖u‖ = 1) : ℝ ≃ₗᵢ[ℝ] (ℝ ∙ u) where
  toFun t := ⟨t • u, Submodule.smul_mem _ t (Submodule.subset_span (Set.mem_singleton u))⟩
  invFun v := inner ℝ u (v : ℂ)
  left_inv t := by
    change inner ℝ u (t • u) = t
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
  right_inv v := by
    ext1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp v.2
    change inner ℝ u (v : ℂ) • u = (v : ℂ)
    rw [← hc, real_inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
  map_add' x y := by ext1; simp [add_smul]
  map_smul' c x := by ext1; simp [mul_smul]
  norm_map' x := by
    change ‖x • u‖ = ‖x‖
    rw [norm_smul, hu, mul_one]

private lemma orthogonalProjectionOnto_eq_lineEquiv (u : ℂ) (hu : ‖u‖ = 1) (z : ℂ) :
    (ℝ ∙ u).orthogonalProjectionOnto z = lineEquiv u hu (inner ℝ u z) := by
  ext1
  rw [← Submodule.starProjection_apply]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
  · intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    change inner ℝ (z - inner ℝ u z • u) (c • u) = 0
    rw [real_inner_smul_right, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hu, one_pow, mul_one, real_inner_comm z u]
    ring

private lemma volume_projection_eq_image (u : ℂ) (hu : ‖u‖ = 1) (K : Set ℂ) :
    volume ((ℝ ∙ u).orthogonalProjectionOnto '' K) =
      volume ((fun z : ℂ => inner ℝ u z) '' K) := by
  have himg : ((ℝ ∙ u).orthogonalProjectionOnto '' K) =
      (lineEquiv u hu) '' ((fun z : ℂ => inner ℝ u z) '' K) := by
    ext v
    simp only [Set.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨inner ℝ u z, ⟨z, hz, rfl⟩, (orthogonalProjectionOnto_eq_lineEquiv u hu z).symm⟩
    · rintro ⟨t, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, orthogonalProjectionOnto_eq_lineEquiv u hu z⟩
  rw [himg]
  let e := (lineEquiv u hu).toMeasurableEquiv
  have hmp : MeasurePreserving e volume volume := (lineEquiv u hu).measurePreserving
  have hpre : (lineEquiv u hu) '' ((fun z : ℂ => inner ℝ u z) '' K) =
      e.symm ⁻¹' ((fun z : ℂ => inner ℝ u z) '' K) :=
    e.toEquiv.image_eq_preimage_symm _
  rw [hpre, ← hmp.symm.map_eq, e.symm.measurableEmbedding.map_apply]

private lemma volume_projection_one (K : Set ℂ) :
    volume ((ℝ ∙ (1 : ℂ)).orthogonalProjectionOnto '' K) = volume (Complex.re '' K) := by
  rw [volume_projection_eq_image 1 norm_one K]
  congr 1; ext r
  simp [Complex.inner]

private lemma volume_projection_I (K : Set ℂ) :
    volume ((ℝ ∙ Complex.I).orthogonalProjectionOnto '' K) = volume (Complex.im '' K) := by
  rw [volume_projection_eq_image Complex.I Complex.norm_I K]
  congr 1; ext r
  simp [Complex.inner]

-- ============================================================================
-- Section 4: 1-Lipschitz CDF compression and Borel measurable sections
-- ============================================================================

private noncomputable def cdfFn (S : Set ℝ) (r : ℝ) : ℝ :=
  (volume (S ∩ Iic r)).toReal / (volume S).toReal

private lemma cdfFn_nonneg (S : Set ℝ) (r : ℝ) : 0 ≤ cdfFn S r := by
  unfold cdfFn; positivity

private lemma cdfFn_le_one (S : Set ℝ) (hS : volume S ≠ ⊤) (hS0 : 0 < (volume S).toReal) (r : ℝ) :
    cdfFn S r ≤ 1 := by
  unfold cdfFn
  rw [div_le_one hS0]
  exact ENNReal.toReal_mono hS (measure_mono inter_subset_left)

private lemma cdfFn_mono (S : Set ℝ) (hS : volume S ≠ ⊤) : Monotone (cdfFn S) := by
  intro r₁ r₂ hle
  unfold cdfFn
  exact div_le_div_of_nonneg_right
    (ENNReal.toReal_mono (ne_top_of_le_ne_top hS (measure_mono inter_subset_left))
      (measure_mono (inter_subset_inter_right S (Iic_subset_Iic.mpr hle))))
    ENNReal.toReal_nonneg

private lemma cdfFn_lipschitz (S : Set ℝ) (hS : volume S ≠ ⊤) (r₁ r₂ : ℝ) :
    (volume S).toReal * |cdfFn S r₂ - cdfFn S r₁| ≤ |r₂ - r₁| := by
  have hordered : ∀ a b : ℝ, a ≤ b →
      (volume S).toReal * (cdfFn S b - cdfFn S a) ≤ b - a := by
    intro a b hab
    by_cases hS0 : (volume S).toReal = 0
    · rw [hS0, zero_mul]; linarith
    · have hm : 0 < (volume S).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hS0)
      unfold cdfFn
      rw [← sub_div, mul_div_cancel₀ _ hm.ne']
      have hsub : S ∩ Iic b ⊆ (S ∩ Iic a) ∪ Ioc a b := by
        intro x hx
        by_cases hxa : x ≤ a
        · exact Or.inl ⟨hx.1, hxa⟩
        · exact Or.inr ⟨lt_of_not_ge hxa, hx.2⟩
      have hmu : volume (S ∩ Iic b) ≤ volume (S ∩ Iic a) + volume (Ioc a b) :=
        le_trans (measure_mono hsub) (measure_union_le _ _)
      have hfin_a : volume (S ∩ Iic a) ≠ ⊤ := ne_top_of_le_ne_top hS (measure_mono inter_subset_left)
      have hfin_Ioc : volume (Ioc a b) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
      have hto : (volume (S ∩ Iic b)).toReal ≤ (volume (S ∩ Iic a)).toReal + (b - a) := by
        have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin_a, hfin_Ioc⟩) hmu
        rw [ENNReal.toReal_add hfin_a hfin_Ioc, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] at h1
        exact h1
      linarith
  rcases le_total r₁ r₂ with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (cdfFn_mono S hS h)), abs_of_nonneg (sub_nonneg.mpr h)]
    exact hordered r₁ r₂ h
  · rw [abs_sub_comm (cdfFn S r₂), abs_sub_comm r₂ r₁,
      abs_of_nonneg (sub_nonneg.mpr (cdfFn_mono S hS h)), abs_of_nonneg (sub_nonneg.mpr h)]
    exact hordered r₂ r₁ h

private lemma cdfFn_continuous (S : Set ℝ) (hS : volume S ≠ ⊤) (hS0 : 0 < (volume S).toReal) :
    Continuous (cdfFn S) := by
  rw [Metric.continuous_iff]
  intro r ε hε
  refine ⟨ε * (volume S).toReal, mul_pos hε hS0, fun x hx => ?_⟩
  have hlip := cdfFn_lipschitz S hS r x
  rw [Real.dist_eq] at hx ⊢
  have : (volume S).toReal * |cdfFn S x - cdfFn S r| < (volume S).toReal * ε := by
    calc (volume S).toReal * |cdfFn S x - cdfFn S r|
        ≤ |x - r| := hlip
      _ < ε * (volume S).toReal := hx
      _ = (volume S).toReal * ε := mul_comm _ _
  exact lt_of_mul_lt_mul_left this hS0.le

private lemma cdfFn_eq_zero_of_subset {S : Set ℝ} {M r : ℝ} (hsub : S ⊆ Icc (-M) M) (hr : r < -M) :
    cdfFn S r = 0 := by
  unfold cdfFn
  have hem : S ∩ Iic r = ∅ := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_empty_iff_false, iff_false, not_and]
    intro hx
    linarith [(hsub hx).1]
  rw [hem, measure_empty, ENNReal.toReal_zero, zero_div]

private lemma cdfFn_eq_one_of_subset {S : Set ℝ} {M r : ℝ} (hsub : S ⊆ Icc (-M) M)
    (hS0 : 0 < (volume S).toReal) (hr : M ≤ r) : cdfFn S r = 1 := by
  unfold cdfFn
  have heq : S ∩ Iic r = S := by
    refine inter_eq_left.mpr fun x hx => le_trans (hsub hx).2 hr
  rw [heq, div_self hS0.ne']

private noncomputable def rinvFn (S : Set ℝ) (s : ℝ) : ℝ :=
  sInf {r : ℝ | s ≤ cdfFn S r}

private lemma rinvFn_properties {S : Set ℝ} (hSc : IsCompact S) (hS0 : 0 < (volume S).toReal) :
    (∀ s ∈ Ioo (0 : ℝ) 1, cdfFn S (rinvFn S s) = s ∧ rinvFn S s ∈ S) ∧
    (∀ s₁ s₂, s₁ ∈ Ioo (0 : ℝ) 1 → s₂ ∈ Ioo (0 : ℝ) 1 → s₁ < s₂ → rinvFn S s₁ < rinvFn S s₂) ∧
    (∀ c : ℝ, {s ∈ Ioo (0 : ℝ) 1 | rinvFn S s ≤ c} = Ioo (0 : ℝ) 1 ∩ Iic (cdfFn S c)) := by
  have hSfin : volume S ≠ ⊤ := hSc.measure_lt_top.ne
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hSc.isBounded
  have hsub : S ⊆ Icc (-R) R := fun x hx => by
    have := abs_le.mp (by simpa [Real.dist_eq] using mem_closedBall_zero_iff.mp (hR hx))
    exact this
  have hcont := cdfFn_continuous S hSfin hS0
  have hbd : ∀ s ∈ Ioo (0 : ℝ) 1, BddBelow {r : ℝ | s ≤ cdfFn S r} := fun s hs => by
    refine ⟨-R - 1, fun r hr => ?_⟩
    by_contra hlt
    push Not at hlt
    have hz := cdfFn_eq_zero_of_subset hsub (by linarith : r < -R)
    have hr' : s ≤ cdfFn S r := hr
    linarith [hs.1]
  have hne : ∀ s ∈ Ioo (0 : ℝ) 1, {r : ℝ | s ≤ cdfFn S r}.Nonempty := fun s hs =>
    ⟨max 0 R, by
      change s ≤ cdfFn S (max 0 R)
      rw [cdfFn_eq_one_of_subset hsub hS0 (le_max_right 0 R)]; exact hs.2.le⟩
  have hcdf_eq : ∀ s ∈ Ioo (0 : ℝ) 1, cdfFn S (rinvFn S s) = s := fun s hs => by
    have hcl : IsClosed {r : ℝ | s ≤ cdfFn S r} := isClosed_le continuous_const hcont
    have hge : s ≤ cdfFn S (rinvFn S s) := hcl.csInf_mem (hne s hs) (hbd s hs)
    refine le_antisymm ?_ hge
    by_contra hgt
    push Not at hgt
    obtain ⟨δ, hδ0, hδ⟩ := (Metric.continuous_iff.mp hcont) (rinvFn S s) (cdfFn S (rinvFn S s) - s) (by linarith)
    have hr' : s ≤ cdfFn S (rinvFn S s - δ / 2) := by
      have hdist : dist (rinvFn S s - δ / 2) (rinvFn S s) < δ := by
        rw [Real.dist_eq, abs_of_neg (by linarith)]
        linarith
      have hd := hδ (rinvFn S s - δ / 2) hdist
      rw [Real.dist_eq] at hd
      linarith [(abs_lt.mp hd).1]
    have hle : rinvFn S s ≤ rinvFn S s - δ / 2 := csInf_le (hbd s hs) hr'
    linarith
  have hmem : ∀ s ∈ Ioo (0 : ℝ) 1, rinvFn S s ∈ S := fun s hs => by
    by_contra hnout
    obtain ⟨δ, hδ0, hδ⟩ := Metric.isOpen_iff.mp hSc.isClosed.isOpen_compl (rinvFn S s) hnout
    have hsub_compl : ∀ x, rinvFn S s - δ / 2 < x → x ≤ rinvFn S s → x ∉ S := fun x hx1 hx2 => by
      apply hδ
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hinter : S ∩ Iic (rinvFn S s) = S ∩ Iic (rinvFn S s - δ / 2) := by
      ext x; simp only [mem_inter_iff, mem_Iic]
      refine ⟨fun ⟨hxS, hx2⟩ => ⟨hxS, ?_⟩, fun ⟨hxS, hx1⟩ => ⟨hxS, by linarith⟩⟩
      by_contra hgt
      push Not at hgt
      exact hsub_compl x hgt hx2 hxS
    have hce : cdfFn S (rinvFn S s - δ / 2) = s := by
      unfold cdfFn
      rw [← hinter]
      exact hcdf_eq s hs
    have hle : rinvFn S s ≤ rinvFn S s - δ / 2 := csInf_le (hbd s hs) (le_of_eq hce.symm)
    linarith
  refine ⟨fun s hs => ⟨hcdf_eq s hs, hmem s hs⟩, ?_, ?_⟩
  · intro s₁ s₂ hs₁ hs₂ hlt
    have hm : rinvFn S s₁ ≤ rinvFn S s₂ :=
      csInf_le (hbd s₁ hs₁) (by change s₁ ≤ cdfFn S (rinvFn S s₂); rw [hcdf_eq s₂ hs₂]; exact hlt.le)
    refine lt_of_le_of_ne hm fun heq => ?_
    have : s₁ = s₂ := by rw [← hcdf_eq s₁ hs₁, ← hcdf_eq s₂ hs₂, heq]
    linarith
  · intro c
    ext s
    simp only [mem_ofPred_eq, mem_inter_iff, mem_Iic]
    refine ⟨fun ⟨hs, hr⟩ => ⟨hs, ?_⟩, fun ⟨hs, hsc⟩ => ⟨hs, ?_⟩⟩
    · rw [← hcdf_eq s hs]
      exact cdfFn_mono S hSfin hr
    · exact csInf_le (hbd s hs) hsc

private lemma rinvFn_measurable {S : Set ℝ} (hSc : IsCompact S) (hS0 : 0 < (volume S).toReal) :
    Measurable (fun t : ℝ => if t ∈ Ioo (0 : ℝ) 1 then rinvFn S (alphaFn t) else 0) := by
  have ⟨_, _, hset⟩ := rinvFn_properties hSc hS0
  refine measurable_of_Iic fun c => ?_
  let f : ℝ → ℝ := fun t => if t ∈ Ioo (0 : ℝ) 1 then rinvFn S (alphaFn t) else 0
  have heq : f ⁻¹' Iic c = (Ioo (0 : ℝ) 1 ∩ alphaFn ⁻¹' (Ioo (0 : ℝ) 1 ∩ Iic (cdfFn S c))) ∪
      (if 0 ≤ c then (Ioo (0 : ℝ) 1)ᶜ else ∅) := by
    ext t
    simp only [f, mem_preimage, mem_Iic, mem_union, mem_inter_iff]
    by_cases ht : t ∈ Ioo (0 : ℝ) 1
    · have ha : alphaFn t ∈ Ioo (0 : ℝ) 1 := by
        have h0 : alphaFn 0 = 0 := by unfold alphaFn; simp
        have h1 : alphaFn 1 = 1 := by unfold alphaFn; simp
        exact ⟨h0 ▸ alphaFn_strictMonoOn ⟨le_rfl, zero_le_one⟩ ⟨ht.1.le, ht.2.le⟩ ht.1,
               h1 ▸ alphaFn_strictMonoOn ⟨ht.1.le, ht.2.le⟩ ⟨zero_le_one, le_rfl⟩ ht.2⟩
      have heqv := congr_arg (fun s => alphaFn t ∈ s) (hset c)
      simp only [mem_ofPred_eq, mem_inter_iff, mem_Iic] at heqv
      split_ifs with h0c <;> simp [ht, ha] <;> exact iff_of_eq (by simpa [ha] using heqv)
    · split_ifs with h0c <;> simp [ht, h0c]
  rw [heq]
  have hcont_alpha : Continuous alphaFn := by
    unfold alphaFn; fun_prop
  refine MeasurableSet.union ?_ ?_
  · exact measurableSet_Ioo.inter ((hcont_alpha.measurable) (measurableSet_Ioo.inter measurableSet_Iic))
  · split_ifs
    · exact measurableSet_Ioo.compl
    · exact MeasurableSet.empty

private noncomputable def vertInf (K : Set ℂ) (r : ℝ) : ℝ :=
  sInf (Complex.im '' (K ∩ {z : ℂ | z.re = r}))

private noncomputable def horizInf (K : Set ℂ) (r : ℝ) : ℝ :=
  sInf (Complex.re '' (K ∩ {z : ℂ | z.im = r}))

private lemma vertInf_mem_and_measurable {K : Set ℂ} (hKc : IsCompact K) :
    (∀ r ∈ Complex.re '' K, (⟨r, vertInf K r⟩ : ℂ) ∈ K) ∧
    (∀ c : ℝ, (Complex.re '' K) ∩ {r : ℝ | vertInf K r ≤ c} =
      Complex.re '' (K ∩ {z : ℂ | z.im ≤ c})) ∧
    Measurable (letI := Classical.propDecidable; fun r => if r ∈ Complex.re '' K then vertInf K r else 0) := by
  classical
  have hmem : ∀ r ∈ Complex.re '' K, (⟨r, vertInf K r⟩ : ℂ) ∈ K := by
    rintro r ⟨z₀, hz₀, rfl⟩
    let S := Complex.im '' (K ∩ {w : ℂ | w.re = z₀.re})
    have hSc : IsCompact S := (hKc.inter_right (isClosed_eq Complex.continuous_re continuous_const)).image Complex.continuous_im
    have hSne : S.Nonempty := ⟨z₀.im, z₀, ⟨hz₀, rfl⟩, rfl⟩
    have hinf : vertInf K z₀.re ∈ S := hSc.isClosed.csInf_mem hSne hSc.bddBelow
    obtain ⟨w, ⟨hwK, hwre⟩, hwim⟩ := hinf
    have hweq : w = ⟨z₀.re, vertInf K z₀.re⟩ := Complex.ext hwre hwim
    exact hweq ▸ hwK
  have hset : ∀ c : ℝ, (Complex.re '' K) ∩ {r : ℝ | vertInf K r ≤ c} =
      Complex.re '' (K ∩ {z : ℂ | z.im ≤ c}) := by
    intro c
    ext r
    simp only [mem_inter_iff, mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨hr, hle⟩
      exact ⟨⟨r, vertInf K r⟩, ⟨hmem r hr, hle⟩, rfl⟩
    · rintro ⟨w, ⟨hwK, hwim⟩, rfl⟩
      refine ⟨⟨w, hwK, rfl⟩, ?_⟩
      let S := Complex.im '' (K ∩ {z : ℂ | z.re = w.re})
      have hSc : IsCompact S := (hKc.inter_right (isClosed_eq Complex.continuous_re continuous_const)).image Complex.continuous_im
      exact le_trans (csInf_le hSc.bddBelow ⟨w, ⟨hwK, rfl⟩, rfl⟩) hwim
  have hmeas : Measurable (fun r => if r ∈ Complex.re '' K then vertInf K r else 0) := by
    refine measurable_of_Iic fun c => ?_
    let f : ℝ → ℝ := fun r => if r ∈ Complex.re '' K then vertInf K r else 0
    have heq : f ⁻¹' Iic c = (Complex.re '' (K ∩ {z : ℂ | z.im ≤ c})) ∪
        (if 0 ≤ c then (Complex.re '' K)ᶜ else ∅) := by
      ext r
      simp only [f, mem_preimage, mem_Iic, mem_union]
      rw [← hset c]
      by_cases hr : r ∈ Complex.re '' K <;> split_ifs with h0c
      · simp [hr]
      · simp [hr]
      · simp [hr, h0c]
      · simp [hr, h0c]
    rw [heq]
    have hc1 : IsClosed (Complex.re '' (K ∩ {z : ℂ | z.im ≤ c})) :=
      ((hKc.inter_right (isClosed_le Complex.continuous_im continuous_const)).image
        Complex.continuous_re).isClosed
    have hc2 : IsClosed (Complex.re '' K) := (hKc.image Complex.continuous_re).isClosed
    refine MeasurableSet.union hc1.measurableSet ?_
    split_ifs
    · exact hc2.measurableSet.compl
    · exact MeasurableSet.empty
  exact ⟨hmem, hset, hmeas⟩

private lemma horizInf_mem_and_measurable {K : Set ℂ} (hKc : IsCompact K) :
    (∀ r ∈ Complex.im '' K, (⟨horizInf K r, r⟩ : ℂ) ∈ K) ∧
    (∀ c : ℝ, (Complex.im '' K) ∩ {r : ℝ | horizInf K r ≤ c} =
      Complex.im '' (K ∩ {z : ℂ | z.re ≤ c})) ∧
    Measurable (letI := Classical.propDecidable; fun r => if r ∈ Complex.im '' K then horizInf K r else 0) := by
  classical
  have hmem : ∀ r ∈ Complex.im '' K, (⟨horizInf K r, r⟩ : ℂ) ∈ K := by
    rintro r ⟨z₀, hz₀, rfl⟩
    let S := Complex.re '' (K ∩ {w : ℂ | w.im = z₀.im})
    have hSc : IsCompact S := (hKc.inter_right (isClosed_eq Complex.continuous_im continuous_const)).image Complex.continuous_re
    have hSne : S.Nonempty := ⟨z₀.re, z₀, ⟨hz₀, rfl⟩, rfl⟩
    have hinf : horizInf K z₀.im ∈ S := hSc.isClosed.csInf_mem hSne hSc.bddBelow
    obtain ⟨w, ⟨hwK, hwim⟩, hwre⟩ := hinf
    have hweq : w = ⟨horizInf K z₀.im, z₀.im⟩ := Complex.ext hwre hwim
    exact hweq ▸ hwK
  have hset : ∀ c : ℝ, (Complex.im '' K) ∩ {r : ℝ | horizInf K r ≤ c} =
      Complex.im '' (K ∩ {z : ℂ | z.re ≤ c}) := by
    intro c
    ext r
    simp only [mem_inter_iff, mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨hr, hle⟩
      exact ⟨⟨horizInf K r, r⟩, ⟨hmem r hr, hle⟩, rfl⟩
    · rintro ⟨w, ⟨hwK, hwre⟩, rfl⟩
      refine ⟨⟨w, hwK, rfl⟩, ?_⟩
      let S := Complex.re '' (K ∩ {z : ℂ | z.im = w.im})
      have hSc : IsCompact S := (hKc.inter_right (isClosed_eq Complex.continuous_im continuous_const)).image Complex.continuous_re
      exact le_trans (csInf_le hSc.bddBelow ⟨w, ⟨hwK, rfl⟩, rfl⟩) hwre
  have hmeas : Measurable (fun r => if r ∈ Complex.im '' K then horizInf K r else 0) := by
    refine measurable_of_Iic fun c => ?_
    let f : ℝ → ℝ := fun r => if r ∈ Complex.im '' K then horizInf K r else 0
    have heq : f ⁻¹' Iic c = (Complex.im '' (K ∩ {z : ℂ | z.re ≤ c})) ∪
        (if 0 ≤ c then (Complex.im '' K)ᶜ else ∅) := by
      ext r
      simp only [f, mem_preimage, mem_Iic, mem_union]
      rw [← hset c]
      by_cases hr : r ∈ Complex.im '' K <;> split_ifs with h0c
      · simp [hr]
      · simp [hr]
      · simp [hr, h0c]
      · simp [hr, h0c]
    rw [heq]
    have hc1 : IsClosed (Complex.im '' (K ∩ {z : ℂ | z.re ≤ c})) :=
      ((hKc.inter_right (isClosed_le Complex.continuous_re continuous_const)).image
        Complex.continuous_im).isClosed
    have hc2 : IsClosed (Complex.im '' K) := (hKc.image Complex.continuous_im).isClosed
    refine MeasurableSet.union hc1.measurableSet ?_
    split_ifs
    · exact hc2.measurableSet.compl
    · exact MeasurableSet.empty
  exact ⟨hmem, hset, hmeas⟩

private noncomputable def lam0 : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

private instance : IsProbabilityMeasure lam0 where
  measure_univ := by
    simp [lam0, Real.volume_Ioo]

private noncomputable def muBool : Measure Bool := (1 / 2 : ENNReal) • Measure.count

private instance : IsProbabilityMeasure muBool where
  measure_univ := by
    have huniv : (Set.univ : Set Bool) = {false} ∪ {true} := by ext x; cases x <;> simp
    rw [muBool, Measure.smul_apply, smul_eq_mul, huniv, measure_union (by simp) (by simp),
      Measure.count_singleton, Measure.count_singleton]
    rw [one_add_one_eq_two, one_div]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

private noncomputable def nuProd : Measure (Bool × ℝ) := muBool.prod lam0

private instance : IsProbabilityMeasure nuProd := by
  unfold nuProd; infer_instance

private lemma integral_muBool (g : Bool → ℝ) :
    ∫ x, g x ∂muBool = (1 / 2 : ℝ) * (g false + g true) := by
  rw [muBool, integral_smul_measure]
  have hint : Integrable g Measure.count := Integrable.of_finite
  have hcnt : ∫ x, g x ∂Measure.count = g false + g true := by
    rw [integral_fintype hint]
    simp only [Measure.real, Measure.count_singleton, ENNReal.toReal_one, smul_eq_mul,
      Fintype.sum_bool]
    ring
  rw [hcnt, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]

private noncomputable def prodSwapMid : (Bool × ℝ) × (Bool × ℝ) ≃ᵐ (Bool × Bool) × (ℝ × ℝ) :=
  (Homeomorph.prodProdProdComm Bool ℝ Bool ℝ).toMeasurableEquiv

private lemma measurePreserving_prodSwapMid :
    MeasurePreserving prodSwapMid (nuProd.prod nuProd) ((muBool.prod muBool).prod (lam0.prod lam0)) := by
  classical
  refine ⟨prodSwapMid.measurable, ?_⟩
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [prodSwapMid.map_apply]
  have hpre : prodSwapMid ⁻¹' (s ×ˢ t) =
      {z : (Bool × ℝ) × (Bool × ℝ) | (z.1.1, z.2.1) ∈ s ∧ (z.1.2, z.2.2) ∈ t} := rfl
  have hm : MeasurableSet (prodSwapMid ⁻¹' (s ×ˢ t)) := prodSwapMid.measurable (hs.prod ht)
  rw [Measure.prod_apply hm]
  have hinner : ∀ z₁ : Bool × ℝ,
      nuProd (Prod.mk z₁ ⁻¹' (prodSwapMid ⁻¹' (s ×ˢ t))) =
        ∫⁻ b₂ : Bool, ∫⁻ t₂ : ℝ,
          (if (z₁.1, b₂) ∈ s ∧ (z₁.2, t₂) ∈ t then (1 : ENNReal) else 0) ∂lam0 ∂muBool := by
    intro z₁
    have hm1 : MeasurableSet {z₂ : Bool × ℝ | (z₁.1, z₂.1) ∈ s ∧ (z₁.2, z₂.2) ∈ t} :=
      measurable_prodMk_left hm
    change nuProd {z₂ : Bool × ℝ | (z₁.1, z₂.1) ∈ s ∧ (z₁.2, z₂.2) ∈ t} = _
    rw [nuProd, Measure.prod_apply hm1]
    refine lintegral_congr fun b₂ => ?_
    rw [← lintegral_indicator_one (measurable_prodMk_left hm1)]
    refine lintegral_congr fun t₂ => ?_
    simp [Set.indicator]
  simp_rw [hinner]
  rw [nuProd, lintegral_prod]
  swap
  · refine (Measurable.lintegral_prod_right (Measurable.lintegral_prod_right ?_)).aemeasurable
    have hms : MeasurableSet {q : ((Bool × ℝ) × Bool) × ℝ |
        (q.1.1.1, q.1.2) ∈ s ∧ (q.1.1.2, q.2) ∈ t} :=
      (hs.preimage ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst))).inter
      (ht.preimage ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd))
    exact Measurable.ite hms measurable_const measurable_const
  have houter : ∀ b₁ : Bool,
      (∫⁻ t₁ : ℝ, ∫⁻ b₂ : Bool, ∫⁻ t₂ : ℝ,
        (if (b₁, b₂) ∈ s ∧ (t₁, t₂) ∈ t then (1 : ENNReal) else 0) ∂lam0 ∂muBool ∂lam0) =
      (∫⁻ b₂ : Bool, (if (b₁, b₂) ∈ s then (1 : ENNReal) else 0) ∂muBool) *
      (∫⁻ t₁ : ℝ, ∫⁻ t₂ : ℝ, (if (t₁, t₂) ∈ t then (1 : ENNReal) else 0) ∂lam0 ∂lam0) := by
    intro b₁
    have hswap : ∀ t₁ : ℝ,
        (∫⁻ b₂ : Bool, ∫⁻ t₂ : ℝ, (if (b₁, b₂) ∈ s ∧ (t₁, t₂) ∈ t then (1 : ENNReal) else 0) ∂lam0 ∂muBool) =
        (∫⁻ b₂ : Bool, (if (b₁, b₂) ∈ s then (1 : ENNReal) else 0) ∂muBool) *
        (∫⁻ t₂ : ℝ, (if (t₁, t₂) ∈ t then (1 : ENNReal) else 0) ∂lam0) := by
      intro t₁
      have hfactor : ∀ b₂ : Bool,
          (∫⁻ t₂ : ℝ, (if (b₁, b₂) ∈ s ∧ (t₁, t₂) ∈ t then (1 : ENNReal) else 0) ∂lam0) =
          (if (b₁, b₂) ∈ s then (1 : ENNReal) else 0) *
          (∫⁻ t₂ : ℝ, (if (t₁, t₂) ∈ t then (1 : ENNReal) else 0) ∂lam0) := by
        intro b₂
        by_cases hbs : (b₁, b₂) ∈ s <;> simp [hbs]
      simp_rw [hfactor]
      exact lintegral_mul_const _ (Measurable.ite (hs.preimage measurable_prodMk_left) measurable_const measurable_const)
    simp_rw [hswap]
    exact lintegral_const_mul _ (Measurable.lintegral_prod_right
      (Measurable.ite ht measurable_const measurable_const))
  simp_rw [houter]
  rw [lintegral_mul_const _ (Measurable.lintegral_prod_right
    (Measurable.ite hs measurable_const measurable_const))]
  congr 1
  · rw [Measure.prod_apply hs]
    refine lintegral_congr fun b₁ => ?_
    rw [← lintegral_indicator_one (measurable_prodMk_left hs)]
    refine lintegral_congr fun b₂ => ?_
    simp [Set.indicator]
  · rw [Measure.prod_apply ht]
    refine lintegral_congr fun t₁ => ?_
    rw [← lintegral_indicator_one (measurable_prodMk_left ht)]
    refine lintegral_congr fun t₂ => ?_
    simp [Set.indicator]

private lemma integrable_nuProd_prod_iff {F : (Bool × ℝ) × (Bool × ℝ) → ℝ} (hFm : Measurable F) :
    Integrable F (nuProd.prod nuProd) ↔
      ∀ b₁ b₂ : Bool, Integrable (fun p : ℝ × ℝ => F ((b₁, p.1), (b₂, p.2))) (lam0.prod lam0) := by
  have heq : Integrable F (nuProd.prod nuProd) ↔
      Integrable (F ∘ prodSwapMid.symm) ((muBool.prod muBool).prod (lam0.prod lam0)) := by
    rw [← measurePreserving_prodSwapMid.symm.integrable_comp_emb prodSwapMid.symm.measurableEmbedding]
  rw [heq, integrable_prod_iff (hFm.comp prodSwapMid.symm.measurable).aestronglyMeasurable]
  have hae : (∀ᵐ x ∂(muBool.prod muBool),
      Integrable (fun p : ℝ × ℝ => (F ∘ prodSwapMid.symm) (x, p)) (lam0.prod lam0)) ↔
      ∀ b₁ b₂ : Bool, Integrable (fun p : ℝ × ℝ => F ((b₁, p.1), (b₂, p.2))) (lam0.prod lam0) := by
    constructor
    · intro h b₁ b₂
      have hpos : (muBool.prod muBool) {(b₁, b₂)} ≠ 0 := by
        rw [← Set.singleton_prod_singleton, Measure.prod_prod]
        simp [muBool, Measure.count_singleton]
      rw [ae_iff] at h
      by_contra hni
      have hsub : {(b₁, b₂)} ⊆
          {x : Bool × Bool | ¬Integrable (fun p : ℝ × ℝ => (F ∘ prodSwapMid.symm) (x, p)) (lam0.prod lam0)} := by
        rintro x rfl; exact hni
      exact hpos (measure_mono_null hsub h)
    · intro h
      exact ae_of_all _ fun ⟨b₁, b₂⟩ => h b₁ b₂
  rw [hae]
  refine ⟨fun h => h.1, fun h => ⟨h, Integrable.of_finite⟩⟩

private lemma integral_nuProd_prod {F : (Bool × ℝ) × (Bool × ℝ) → ℝ}
    (hFi : Integrable F (nuProd.prod nuProd)) :
    ∫ z, F z ∂(nuProd.prod nuProd) =
      (1 / 4 : ℝ) *
        ((∫ p : ℝ × ℝ, F ((false, p.1), (false, p.2)) ∂(lam0.prod lam0)) +
         (∫ p : ℝ × ℝ, F ((false, p.1), (true, p.2)) ∂(lam0.prod lam0)) +
         (∫ p : ℝ × ℝ, F ((true, p.1), (false, p.2)) ∂(lam0.prod lam0)) +
         (∫ p : ℝ × ℝ, F ((true, p.1), (true, p.2)) ∂(lam0.prod lam0))) := by
  have hcomp : ∫ z, F z ∂(nuProd.prod nuProd) =
      ∫ w : (Bool × Bool) × (ℝ × ℝ), (F ∘ prodSwapMid.symm) w
        ∂((muBool.prod muBool).prod (lam0.prod lam0)) := by
    symm
    exact measurePreserving_prodSwapMid.symm.integral_comp prodSwapMid.symm.measurableEmbedding F
  have hFi' : Integrable (F ∘ prodSwapMid.symm)
      ((muBool.prod muBool).prod (lam0.prod lam0)) := by
    rwa [measurePreserving_prodSwapMid.symm.integrable_comp_emb prodSwapMid.symm.measurableEmbedding]
  rw [hcomp, integral_prod _ hFi', integral_prod _ hFi'.integral_prod_left]
  simp only [integral_muBool, Function.comp_def]
  have hsymm : ∀ b₁ b₂ (y : ℝ × ℝ), prodSwapMid.symm ((b₁, b₂), y) = ((b₁, y.1), (b₂, y.2)) :=
    fun _ _ _ => rfl
  simp_rw [hsymm]
  ring

private lemma ae_nuProd_prod_iff {P : (Bool × ℝ) × (Bool × ℝ) → Prop}
    (hPm : MeasurableSet {z | P z}) :
    (∀ᵐ z ∂(nuProd.prod nuProd), P z) ↔
      ∀ b₁ b₂ : Bool, ∀ᵐ p ∂(lam0.prod lam0), P ((b₁, p.1), (b₂, p.2)) := by
  have hpre : prodSwapMid.symm ⁻¹' {z | P z}ᶜ =
      {w : (Bool × Bool) × (ℝ × ℝ) | P ((w.1.1, w.2.1), (w.1.2, w.2.2))}ᶜ := rfl
  have hm_w : MeasurableSet {w : (Bool × Bool) × (ℝ × ℝ) | P ((w.1.1, w.2.1), (w.1.2, w.2.2))} := by
    exact prodSwapMid.symm.measurable hPm
  have hzero : (nuProd.prod nuProd) {z | ¬ P z} =
      ((muBool.prod muBool).prod (lam0.prod lam0))
        {w : (Bool × Bool) × (ℝ × ℝ) | ¬ P ((w.1.1, w.2.1), (w.1.2, w.2.2))} := by
    change (nuProd.prod nuProd) {z | P z}ᶜ =
      ((muBool.prod muBool).prod (lam0.prod lam0)) {w | P ((w.1.1, w.2.1), (w.1.2, w.2.2))}ᶜ
    rw [← measurePreserving_prodSwapMid.symm.measure_preimage hPm.compl.nullMeasurableSet, hpre]
  rw [ae_iff, hzero, ← ae_iff, Measure.ae_prod_iff_ae_ae hm_w]
  constructor
  · intro h b₁ b₂
    have hpos : (muBool.prod muBool) {(b₁, b₂)} ≠ 0 := by
      rw [← Set.singleton_prod_singleton, Measure.prod_prod]
      simp [muBool, Measure.count_singleton]
    rw [ae_iff] at h
    by_contra hn
    have hsub : {(b₁, b₂)} ⊆
        {x : Bool × Bool | ¬ ∀ᵐ p ∂(lam0.prod lam0), P ((x.1, p.1), (x.2, p.2))} := by
      rintro x rfl; exact hn
    exact hpos (measure_mono_null hsub h)
  · intro h
    exact ae_of_all _ fun ⟨b₁, b₂⟩ => h b₁ b₂

private lemma measurePreserving_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    MeasurePreserving (fun ω : Fin n → Bool × ℝ => (ω i, ω j))
      (Measure.pi fun _ : Fin n => nuProd) (nuProd.prod nuProd) := by
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) (hs.prod ht)]
  let f : Fin n → Set (Bool × ℝ) := fun k => if k = i then s else if k = j then t else Set.univ
  have hpre : (fun ω : Fin n → Bool × ℝ => (ω i, ω j)) ⁻¹' (s ×ˢ t) = Set.univ.pi f := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left, f]
    constructor
    · rintro ⟨hi, hj⟩ k
      split_ifs with hki hkj
      · subst hki; exact hi
      · subst hkj; exact hj
      · trivial
    · intro hk
      refine ⟨?_, ?_⟩
      · simpa using hk i
      · have h1 := hk j
        simp [hij.symm] at h1
        exact h1
  rw [hpre, Measure.pi_pi]
  have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  rw [← Finset.mul_prod_erase Finset.univ (fun k => nuProd (f k)) hi_mem]
  have hfi : nuProd (f i) = nuProd s := by simp [f]
  have hj_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  rw [← Finset.mul_prod_erase (Finset.univ.erase i) (fun k => nuProd (f k)) hj_mem]
  have hfj : nuProd (f j) = nuProd t := by simp [f, hij.symm]
  have hrest : ∏ k ∈ (Finset.univ.erase i).erase j, nuProd (f k) = 1 := by
    refine Finset.prod_eq_one fun k hk => ?_
    rw [Finset.mem_erase, Finset.mem_erase] at hk
    simp [f, hk.2.1, hk.1]
  rw [hfi, hfj, hrest, mul_one]

private noncomputable def pFn (K : Set ℂ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  if t ∈ Ioo (0 : ℝ) 1 then
    ⟨rinvFn (Complex.re '' K) (alphaFn t), vertInf K (rinvFn (Complex.re '' K) (alphaFn t))⟩
  else z₀

private noncomputable def qFn (K : Set ℂ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  if t ∈ Ioo (0 : ℝ) 1 then
    ⟨horizInf K (rinvFn (Complex.im '' K) (alphaFn t)), rinvFn (Complex.im '' K) (alphaFn t)⟩
  else z₀

private noncomputable def yFn (K : Set ℂ) (z₀ : ℂ) (t : ℝ) : ℝ :=
  cdfFn (Complex.im '' K) (pFn K z₀ t).im

private noncomputable def uFn (K : Set ℂ) (z₀ : ℂ) (t : ℝ) : ℝ :=
  cdfFn (Complex.re '' K) (qFn K z₀ t).re

private noncomputable def phiMap (K : Set ℂ) (z₀ : ℂ) (ω : Bool × ℝ) : ℂ :=
  if ω.1 then qFn K z₀ ω.2 else pFn K z₀ ω.2

private noncomputable def e1Rat (x₁ y₁ x₂ y₂ : ℝ) : ℝ :=
  let dx := x₁ - x₂
  let dy := y₁ - y₂
  if dx = 0 then 0 else (dy ^ 2 / dx ^ 2) / (2 + dy ^ 2 / dx ^ 2)

private noncomputable def e12Rat (x y u v : ℝ) : ℝ :=
  let dx := |x - u|
  let dy := |y - v|
  if dx = 0 ∨ dy = 0 then 0 else ((dx - dy) / (dx + dy)) ^ 2

private lemma e1Rat_bounds (x₁ y₁ x₂ y₂ : ℝ) :
    0 ≤ e1Rat x₁ y₁ x₂ y₂ ∧ e1Rat x₁ y₁ x₂ y₂ ≤ 1 := by
  unfold e1Rat
  dsimp only
  split_ifs with h
  · constructor <;> norm_num
  · have hq : 0 ≤ (y₁ - y₂) ^ 2 / (x₁ - x₂) ^ 2 := by positivity
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by linarith)]
    linarith

private lemma e12Rat_bounds (x y u v : ℝ) :
    0 ≤ e12Rat x y u v ∧ e12Rat x y u v ≤ 1 := by
  unfold e12Rat
  dsimp only
  split_ifs with h
  · constructor <;> norm_num
  · refine ⟨sq_nonneg _, ?_⟩
    have h1 : 0 ≤ |x - u| := abs_nonneg _
    have h2 : 0 ≤ |y - v| := abs_nonneg _
    have hpos : 0 < |x - u| + |y - v| := by
      rcases not_or.mp h with ⟨ha, hb⟩
      linarith [abs_pos.mpr (abs_ne_zero.mp ha), abs_pos.mpr (abs_ne_zero.mp hb)]
    rw [sq_le_one_iff_abs_le_one, abs_div, abs_of_pos hpos, div_le_one hpos, abs_le]
    constructor <;> linarith

private noncomputable def energyRat (y u : ℝ → ℝ) : ℝ :=
  (1 / 4 : ℝ) * (∫ p : ℝ × ℝ, e1Rat (alphaFn p.1) (y p.1) (alphaFn p.2) (y p.2) ∂(lam0.prod lam0)) +
  (1 / 4 : ℝ) * (∫ p : ℝ × ℝ, e1Rat (alphaFn p.1) (u p.1) (alphaFn p.2) (u p.2) ∂(lam0.prod lam0)) +
  (1 / 2 : ℝ) * (∫ p : ℝ × ℝ, e12Rat (alphaFn p.1) (y p.1) (u p.2) (alphaFn p.2) ∂(lam0.prod lam0))

private lemma measurable_pFn {K : Set ℂ} (hKc : IsCompact K) (hRe0 : 0 < (volume (Complex.re '' K)).toReal)
    (z₀ : ℂ) : Measurable (pFn K z₀) := by
  classical
  have hReC : IsCompact (Complex.re '' K) := hKc.image Complex.continuous_re
  have hr := rinvFn_measurable hReC hRe0
  have ⟨_, _, hg⟩ := vertInf_mem_and_measurable hKc
  let r₁ : ℝ → ℝ := fun t => if t ∈ Ioo (0 : ℝ) 1 then rinvFn (Complex.re '' K) (alphaFn t) else 0
  let g₁ : ℝ → ℝ := fun r => if r ∈ Complex.re '' K then vertInf K r else 0
  have hpair : Measurable (fun t : ℝ => (r₁ t : ℂ) + (g₁ (r₁ t) : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.measurable.comp hr).add
      ((Complex.continuous_ofReal.measurable.comp (hg.comp hr)).mul measurable_const)
  have hm_ite : Measurable (fun t : ℝ =>
      if t ∈ Ioo (0 : ℝ) 1 then (r₁ t : ℂ) + (g₁ (r₁ t) : ℂ) * Complex.I else z₀) :=
    Measurable.ite measurableSet_Ioo hpair measurable_const
  have heq : pFn K z₀ = fun t : ℝ =>
      if t ∈ Ioo (0 : ℝ) 1 then (r₁ t : ℂ) + (g₁ (r₁ t) : ℂ) * Complex.I else z₀ := by
    ext t
    by_cases ht : t ∈ Ioo (0 : ℝ) 1
    · have ha_mem : alphaFn t ∈ Ioo (0 : ℝ) 1 := by
        have h0 : alphaFn 0 = 0 := by unfold alphaFn; simp
        have h1 : alphaFn 1 = 1 := by unfold alphaFn; simp
        exact ⟨h0 ▸ alphaFn_strictMonoOn ⟨le_rfl, zero_le_one⟩ ⟨ht.1.le, ht.2.le⟩ ht.1,
               h1 ▸ alphaFn_strictMonoOn ⟨ht.1.le, ht.2.le⟩ ⟨zero_le_one, le_rfl⟩ ht.2⟩
      have hr_mem : rinvFn (Complex.re '' K) (alphaFn t) ∈ Complex.re '' K :=
        ((rinvFn_properties hReC hRe0).1 (alphaFn t) ha_mem).2
      simp only [pFn, r₁, g₁, ht, hr_mem, ↓reduceIte]
      apply Complex.ext <;> simp
    · simp [pFn, ht]
  rw [heq]
  exact hm_ite

private lemma measurable_qFn {K : Set ℂ} (hKc : IsCompact K) (hIm0 : 0 < (volume (Complex.im '' K)).toReal)
    (z₀ : ℂ) : Measurable (qFn K z₀) := by
  classical
  have hImC : IsCompact (Complex.im '' K) := hKc.image Complex.continuous_im
  have hr := rinvFn_measurable hImC hIm0
  have ⟨_, _, hg⟩ := horizInf_mem_and_measurable hKc
  let r₁ : ℝ → ℝ := fun t => if t ∈ Ioo (0 : ℝ) 1 then rinvFn (Complex.im '' K) (alphaFn t) else 0
  let g₁ : ℝ → ℝ := fun r => if r ∈ Complex.im '' K then horizInf K r else 0
  have hpair : Measurable (fun t : ℝ => (g₁ (r₁ t) : ℂ) + (r₁ t : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.measurable.comp (hg.comp hr)).add
      ((Complex.continuous_ofReal.measurable.comp hr).mul measurable_const)
  have hm_ite : Measurable (fun t : ℝ =>
      if t ∈ Ioo (0 : ℝ) 1 then (g₁ (r₁ t) : ℂ) + (r₁ t : ℂ) * Complex.I else z₀) :=
    Measurable.ite measurableSet_Ioo hpair measurable_const
  have heq : qFn K z₀ = fun t : ℝ =>
      if t ∈ Ioo (0 : ℝ) 1 then (g₁ (r₁ t) : ℂ) + (r₁ t : ℂ) * Complex.I else z₀ := by
    ext t
    by_cases ht : t ∈ Ioo (0 : ℝ) 1
    · have ha_mem : alphaFn t ∈ Ioo (0 : ℝ) 1 := by
        have h0 : alphaFn 0 = 0 := by unfold alphaFn; simp
        have h1 : alphaFn 1 = 1 := by unfold alphaFn; simp
        exact ⟨h0 ▸ alphaFn_strictMonoOn ⟨le_rfl, zero_le_one⟩ ⟨ht.1.le, ht.2.le⟩ ht.1,
               h1 ▸ alphaFn_strictMonoOn ⟨ht.1.le, ht.2.le⟩ ⟨zero_le_one, le_rfl⟩ ht.2⟩
      have hr_mem : rinvFn (Complex.im '' K) (alphaFn t) ∈ Complex.im '' K :=
        ((rinvFn_properties hImC hIm0).1 (alphaFn t) ha_mem).2
      simp only [qFn, r₁, g₁, ht, hr_mem, ↓reduceIte]
      apply Complex.ext <;> simp
    · simp [qFn, ht]
  rw [heq]
  exact hm_ite

private lemma alphaFn_ne_const_ae (c : ℝ) : ∀ᵐ t ∂lam0, alphaFn t ≠ c := by
  have hsubsing : ({t : ℝ | t ∈ Ioo (0 : ℝ) 1 ∧ alphaFn t = c}).Subsingleton := by
    intro t₁ ht₁ t₂ ht₂
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := alphaFn_strictMonoOn ⟨ht₁.1.1.le, ht₁.1.2.le⟩ ⟨ht₂.1.1.le, ht₂.1.2.le⟩ hlt
      linarith [ht₁.2, ht₂.2]
    · have := alphaFn_strictMonoOn ⟨ht₂.1.1.le, ht₂.1.2.le⟩ ⟨ht₁.1.1.le, ht₁.1.2.le⟩ hlt
      linarith [ht₁.2, ht₂.2]
  have hcont : Continuous alphaFn := by unfold alphaFn; fun_prop
  have hnullset : NullMeasurableSet {a | ¬alphaFn a ≠ c} (volume.restrict (Ioo (0 : ℝ) 1)) := by
    rw [show {a : ℝ | ¬alphaFn a ≠ c} = {a : ℝ | alphaFn a = c} by ext; simp]
    exact (isClosed_eq hcont continuous_const).measurableSet.nullMeasurableSet
  rw [ae_iff, lam0, Measure.restrict_apply₀ hnullset]
  refine measure_mono_null (fun t ht => ?_) (hsubsing.measure_zero volume)
  exact ⟨ht.2, not_not.mp ht.1⟩

private lemma integrable_and_integral_log_alpha_sub_fn {g : ℝ → ℝ} (hgm : Measurable g)
    (hg : ∀ t, g t ∈ Icc (0 : ℝ) 1) :
    Integrable (fun p : ℝ × ℝ => Real.log |alphaFn p.1 - g p.2|) (lam0.prod lam0) ∧
    (∫ p : ℝ × ℝ, Real.log |alphaFn p.1 - g p.2| ∂(lam0.prod lam0)) = -2 * Real.log 2 := by
  have hcont : Continuous alphaFn := by unfold alphaFn; fun_prop
  have hm : Measurable (fun p : ℝ × ℝ => Real.log |alphaFn p.1 - g p.2|) :=
    Real.measurable_log.comp (continuous_abs.measurable.comp ((hcont.measurable.comp measurable_fst).sub (hgm.comp measurable_snd)))
  have hneg : ∀ p : ℝ × ℝ, Real.log |alphaFn p.1 - g p.2| ≤ 0 := fun p => by
    apply Real.log_nonpos (abs_nonneg _)
    rw [abs_le]
    have ha := alphaFn_mem_Icc p.1
    have hgp := hg p.2
    constructor <;> linarith [ha.1, ha.2, hgp.1, hgp.2]
  have hint : Integrable (fun p : ℝ × ℝ => Real.log |alphaFn p.1 - g p.2|) (lam0.prod lam0) := by
    rw [integrable_prod_iff' hm.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun t₂ => (integral_log_abs_alpha_sub (hg t₂)).1.integrable, ?_⟩
    have hnorm : ∀ t₂ : ℝ, (∫ t₁ : ℝ, ‖Real.log |alphaFn t₁ - g t₂|‖ ∂lam0) = 2 * Real.log 2 := fun t₂ => by
      have hsub := integral_log_abs_alpha_sub (hg t₂)
      calc (∫ t₁ : ℝ, ‖Real.log |alphaFn t₁ - g t₂|‖ ∂lam0)
          = ∫ t₁ : ℝ, (-Real.log |alphaFn t₁ - g t₂|) ∂lam0 := by
            refine integral_congr_ae (ae_of_all _ fun t₁ => ?_)
            dsimp only
            rw [Real.norm_eq_abs, abs_of_nonpos (hneg (t₁, t₂))]
        _ = -(∫ t₁ : ℝ, Real.log |alphaFn t₁ - g t₂| ∂lam0) := integral_neg _
        _ = -(-2 * Real.log 2) := by rw [lam0, hsub.2]
        _ = 2 * Real.log 2 := by ring
    simp_rw [hnorm]
    exact integrable_const _
  refine ⟨hint, ?_⟩
  rw [integral_prod_symm _ hint]
  have hinner : ∀ t₂ : ℝ, (∫ t₁ : ℝ, Real.log |alphaFn t₁ - g t₂| ∂lam0) = -2 * Real.log 2 :=
    fun t₂ => (integral_log_abs_alpha_sub (hg t₂)).2
  simp_rw [hinner]
  simp

private lemma card_Ioi_sum (n : ℕ) :
    (∑ i : Fin n, (Finset.Ioi i).card : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  have hdouble : 2 * ∑ i : Fin n, (Finset.Ioi i).card = n * (n - 1) := by
    have hsum1 : ∑ i : Fin n, (Finset.Ioi i).card =
        ∑ i : Fin n, ∑ j : Fin n, if i < j then 1 else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hs : Finset.Ioi i = Finset.univ.filter (fun j : Fin n => i < j) := by ext; simp
      rw [hs, Finset.card_filter]
    have hsum2 : ∑ i : Fin n, (Finset.Ioi i).card =
        ∑ i : Fin n, ∑ j : Fin n, if j < i then 1 else 0 := by
      rw [hsum1, Finset.sum_comm]
    have htot : (∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℕ) else 0) +
        (∑ i : Fin n, ∑ j : Fin n, if j < i then 1 else 0) +
        ∑ i : Fin n, ∑ j : Fin n, (if i = j then (1 : ℕ) else 0) = n * n := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      calc ∑ i : Fin n, ((∑ j : Fin n, if i < j then 1 else 0) +
            (∑ j : Fin n, if j < i then 1 else 0) + (∑ j : Fin n, if i = j then 1 else 0))
          = ∑ i : Fin n, ∑ j : Fin n, (1 : ℕ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_
            rcases lt_trichotomy i j with h | rfl | h
            · simp [h, ne_of_lt h, not_lt_of_gt h]
            · simp
            · simp [h, ne_of_gt h, not_lt_of_gt h]
        _ = n * n := by simp
    have hi : ∀ i : Fin n, (∑ j : Fin n, if i = j then (1 : ℕ) else 0) = 1 := fun i => by simp
    simp_rw [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at htot
    have hnn : n * n = n * (n - 1) + n := by
      cases n with
      | zero => simp
      | succ k => simp [Nat.mul_succ, Nat.add_comm]
    omega
  have hcast : (2 : ℝ) * (∑ i : Fin n, ((Finset.Ioi i).card : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) := by
    rcases n with _ | k
    · simp
    · have h2 : (2 * ∑ i : Fin (k + 1), (Finset.Ioi i).card : ℕ) = (k + 1) * k := by
        simpa using hdouble
      have h2r : ((2 * ∑ i : Fin (k + 1), (Finset.Ioi i).card : ℕ) : ℝ) = (((k + 1) * k : ℕ) : ℝ) := by
        exact_mod_cast h2
      push_cast at h2r ⊢
      linarith
  linarith

private lemma energyRat_upper_bound {f : ℂ[X]} (hf : f.Monic) (hd : 1 ≤ f.degree)
    (hReGt : (3.3 : ℝ) < (volume (Complex.re '' Erdos1043.levelSet f)).toReal)
    (hImGt : (3.3 : ℝ) < (volume (Complex.im '' Erdos1043.levelSet f)).toReal) :
    ∃ z₀ ∈ Erdos1043.levelSet f,
      (∀ t, yFn (Erdos1043.levelSet f) z₀ t ∈ Icc (0 : ℝ) 1) ∧
      (∀ t, uFn (Erdos1043.levelSet f) z₀ t ∈ Icc (0 : ℝ) 1) ∧
      Measurable (yFn (Erdos1043.levelSet f) z₀) ∧
      Measurable (uFn (Erdos1043.levelSet f) z₀) ∧
      energyRat (yFn (Erdos1043.levelSet f) z₀) (uFn (Erdos1043.levelSet f) z₀) ≤
        94079 / (4 * 1185921) := by
  let K := Erdos1043.levelSet f
  have hKc : IsCompact K := isCompact_levelSet hf hd
  have hReC : IsCompact (Complex.re '' K) := hKc.image Complex.continuous_re
  have hImC : IsCompact (Complex.im '' K) := hKc.image Complex.continuous_im
  let a : ℝ := (volume (Complex.re '' K)).toReal
  let b : ℝ := (volume (Complex.im '' K)).toReal
  have ha_gt : (3.3 : ℝ) < a := hReGt
  have hb_gt : (3.3 : ℝ) < b := hImGt
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hReFin : volume (Complex.re '' K) ≠ ⊤ := hReC.measure_lt_top.ne
  have hImFin : volume (Complex.im '' K) ≠ ⊤ := hImC.measure_lt_top.ne
  have hKne : K.Nonempty := by
    by_contra hem
    rw [not_nonempty_iff_eq_empty] at hem
    have : a = 0 := by simp [a, K, hem]
    linarith
  obtain ⟨z₀, hz₀⟩ := hKne
  let p := pFn K z₀
  let q := qFn K z₀
  let y := yFn K z₀
  let u := uFn K z₀
  let phi := phiMap K z₀
  have hp_mem : ∀ t, p t ∈ K := fun t => by
    dsimp [p, pFn]
    split_ifs with ht
    · have ha_mem : alphaFn t ∈ Ioo (0 : ℝ) 1 := by
        have h0 : alphaFn 0 = 0 := by unfold alphaFn; simp
        have h1 : alphaFn 1 = 1 := by unfold alphaFn; simp
        exact ⟨h0 ▸ alphaFn_strictMonoOn ⟨le_rfl, zero_le_one⟩ ⟨ht.1.le, ht.2.le⟩ ht.1,
               h1 ▸ alphaFn_strictMonoOn ⟨ht.1.le, ht.2.le⟩ ⟨zero_le_one, le_rfl⟩ ht.2⟩
      have hrinv := (rinvFn_properties hReC ha0).1 (alphaFn t) ha_mem
      exact (vertInf_mem_and_measurable hKc).1 _ hrinv.2
    · exact hz₀
  have hq_mem : ∀ t, q t ∈ K := fun t => by
    dsimp [q, qFn]
    split_ifs with ht
    · have ha_mem : alphaFn t ∈ Ioo (0 : ℝ) 1 := by
        have h0 : alphaFn 0 = 0 := by unfold alphaFn; simp
        have h1 : alphaFn 1 = 1 := by unfold alphaFn; simp
        exact ⟨h0 ▸ alphaFn_strictMonoOn ⟨le_rfl, zero_le_one⟩ ⟨ht.1.le, ht.2.le⟩ ht.1,
               h1 ▸ alphaFn_strictMonoOn ⟨ht.1.le, ht.2.le⟩ ⟨zero_le_one, le_rfl⟩ ht.2⟩
      have hrinv := (rinvFn_properties hImC hb0).1 (alphaFn t) ha_mem
      exact (horizInf_mem_and_measurable hKc).1 _ hrinv.2
    · exact hz₀
  have hphi_mem : ∀ ω, phi ω ∈ K := fun ⟨bw, t⟩ => by
    dsimp [phi, phiMap]; cases bw <;> [exact hp_mem t; exact hq_mem t]
  have hy_mem : ∀ t, y t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨cdfFn_nonneg _ _, cdfFn_le_one _ hImFin hb0 _⟩
  have hu_mem : ∀ t, u t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨cdfFn_nonneg _ _, cdfFn_le_one _ hReFin ha0 _⟩
  have hm_p : Measurable p := measurable_pFn hKc ha0 z₀
  have hm_q : Measurable q := measurable_qFn hKc hb0 z₀
  have hm_y : Measurable y := (cdfFn_continuous _ hImFin hb0).measurable.comp (Complex.continuous_im.measurable.comp hm_p)
  have hm_u : Measurable u := (cdfFn_continuous _ hReFin ha0).measurable.comp (Complex.continuous_re.measurable.comp hm_q)
  have hm_phi : Measurable phi := Measurable.ite (measurable_fst (measurableSet_singleton true))
    (hm_q.comp measurable_snd) (hm_p.comp measurable_snd)
  have hp_re : ∀ t ∈ Ioo (0 : ℝ) 1, cdfFn (Complex.re '' K) (p t).re = alphaFn t := fun t ht => by
    have ha_mem : alphaFn t ∈ Ioo (0 : ℝ) 1 := by
      have h0 : alphaFn 0 = 0 := by unfold alphaFn; simp
      have h1 : alphaFn 1 = 1 := by unfold alphaFn; simp
      exact ⟨h0 ▸ alphaFn_strictMonoOn ⟨le_rfl, zero_le_one⟩ ⟨ht.1.le, ht.2.le⟩ ht.1,
             h1 ▸ alphaFn_strictMonoOn ⟨ht.1.le, ht.2.le⟩ ⟨zero_le_one, le_rfl⟩ ht.2⟩
    dsimp [p, pFn]
    rw [if_pos ht]
    exact ((rinvFn_properties hReC ha0).1 (alphaFn t) ha_mem).1
  have hq_im : ∀ t ∈ Ioo (0 : ℝ) 1, cdfFn (Complex.im '' K) (q t).im = alphaFn t := fun t ht => by
    have ha_mem : alphaFn t ∈ Ioo (0 : ℝ) 1 := by
      have h0 : alphaFn 0 = 0 := by unfold alphaFn; simp
      have h1 : alphaFn 1 = 1 := by unfold alphaFn; simp
      exact ⟨h0 ▸ alphaFn_strictMonoOn ⟨le_rfl, zero_le_one⟩ ⟨ht.1.le, ht.2.le⟩ ht.1,
             h1 ▸ alphaFn_strictMonoOn ⟨ht.1.le, ht.2.le⟩ ⟨zero_le_one, le_rfl⟩ ht.2⟩
    dsimp [q, qFn]
    rw [if_pos ht]
    exact ((rinvFn_properties hImC hb0).1 (alphaFn t) ha_mem).1
  have hlip_pp_re : ∀ t₁ ∈ Ioo (0 : ℝ) 1, ∀ t₂ ∈ Ioo (0 : ℝ) 1,
      a * |alphaFn t₁ - alphaFn t₂| ≤ |(p t₁).re - (p t₂).re| := fun t₁ ht₁ t₂ ht₂ => by
    simpa [a, hp_re t₁ ht₁, hp_re t₂ ht₂, abs_sub_comm] using
      cdfFn_lipschitz (Complex.re '' K) hReFin (p t₂).re (p t₁).re
  have hlip_y : ∀ t₁ t₂ : ℝ, b * |y t₁ - y t₂| ≤ |(p t₁).im - (p t₂).im| := fun t₁ t₂ => by
    simpa [b, y, yFn, abs_sub_comm] using
      cdfFn_lipschitz (Complex.im '' K) hImFin (p t₂).im (p t₁).im
  have hlip_qq_im : ∀ t₁ ∈ Ioo (0 : ℝ) 1, ∀ t₂ ∈ Ioo (0 : ℝ) 1,
      b * |alphaFn t₁ - alphaFn t₂| ≤ |(q t₁).im - (q t₂).im| := fun t₁ ht₁ t₂ ht₂ => by
    simpa [b, hq_im t₁ ht₁, hq_im t₂ ht₂, abs_sub_comm] using
      cdfFn_lipschitz (Complex.im '' K) hImFin (q t₂).im (q t₁).im
  have hlip_u : ∀ t₁ t₂ : ℝ, a * |u t₁ - u t₂| ≤ |(q t₁).re - (q t₂).re| := fun t₁ t₂ => by
    simpa [a, u, uFn, abs_sub_comm] using
      cdfFn_lipschitz (Complex.re '' K) hReFin (q t₂).re (q t₁).re
  have hlip_pq_re : ∀ t₁ ∈ Ioo (0 : ℝ) 1, ∀ t₂ : ℝ,
      a * |alphaFn t₁ - u t₂| ≤ |(p t₁).re - (q t₂).re| := fun t₁ ht₁ t₂ => by
    simpa [a, u, uFn, hp_re t₁ ht₁, abs_sub_comm] using
      cdfFn_lipschitz (Complex.re '' K) hReFin (q t₂).re (p t₁).re
  have hlip_pq_im : ∀ t₁ : ℝ, ∀ t₂ ∈ Ioo (0 : ℝ) 1,
      b * |y t₁ - alphaFn t₂| ≤ |(p t₁).im - (q t₂).im| := fun t₁ t₂ ht₂ => by
    simpa [b, y, yFn, hq_im t₂ ht₂, abs_sub_comm] using
      cdfFn_lipschitz (Complex.im '' K) hImFin (q t₂).im (p t₁).im
  have hcont_alpha : Continuous alphaFn := by unfold alphaFn; fun_prop
  have hae_Ioo_prod : ∀ᵐ pr : ℝ × ℝ ∂(lam0.prod lam0), pr.1 ∈ Ioo (0 : ℝ) 1 ∧ pr.2 ∈ Ioo (0 : ℝ) 1 := by
    have hms : MeasurableSet {pr : ℝ × ℝ | pr.1 ∈ Ioo (0 : ℝ) 1 ∧ pr.2 ∈ Ioo (0 : ℝ) 1} :=
      (measurableSet_Ioo.preimage measurable_fst).inter (measurableSet_Ioo.preimage measurable_snd)
    refine (Measure.ae_prod_iff_ae_ae hms).mpr ?_
    have h1 : ∀ᵐ t ∂lam0, t ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
    filter_upwards [h1] with t₁ ht₁
    filter_upwards [h1] with t₂ ht₂
    exact ⟨ht₁, ht₂⟩
  have hae_alpha_diff : ∀ᵐ pr : ℝ × ℝ ∂(lam0.prod lam0), alphaFn pr.1 ≠ alphaFn pr.2 := by
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards with t₁
      exact (alphaFn_ne_const_ae (alphaFn t₁)).mono fun t₂ ht₂ => Ne.symm ht₂
    · exact (isClosed_eq (hcont_alpha.comp continuous_fst) (hcont_alpha.comp continuous_snd)).measurableSet.compl
  have hae_alpha_u : ∀ᵐ pr : ℝ × ℝ ∂(lam0.prod lam0), alphaFn pr.1 ≠ u pr.2 := by
    have hm_au : MeasurableSet {pr : ℝ × ℝ | alphaFn pr.2 ≠ u pr.1} := by
      have hm1 : Measurable (fun pr : ℝ × ℝ => (alphaFn pr.2, u pr.1)) :=
        (hcont_alpha.measurable.comp measurable_snd).prodMk (hm_u.comp measurable_fst)
      exact (hm1 isClosed_diagonal.measurableSet).compl
    have hs : ∀ᵐ pr : ℝ × ℝ ∂(lam0.prod lam0), alphaFn pr.2 ≠ u pr.1 := by
      rw [Measure.ae_prod_iff_ae_ae hm_au]
      filter_upwards with t₂
      exact alphaFn_ne_const_ae (u t₂)
    exact (Measure.measurePreserving_swap : MeasurePreserving Prod.swap (lam0.prod lam0) (lam0.prod lam0)).quasiMeasurePreserving.ae hs
  have hae_y_alpha : ∀ᵐ pr : ℝ × ℝ ∂(lam0.prod lam0), y pr.1 ≠ alphaFn pr.2 := by
    have hm_ya : MeasurableSet {pr : ℝ × ℝ | y pr.1 ≠ alphaFn pr.2} := by
      have hm1 : Measurable (fun pr : ℝ × ℝ => (y pr.1, alphaFn pr.2)) :=
        (hm_y.comp measurable_fst).prodMk (hcont_alpha.measurable.comp measurable_snd)
      exact (hm1 isClosed_diagonal.measurableSet).compl
    rw [Measure.ae_prod_iff_ae_ae hm_ya]
    filter_upwards with t₁
    exact (alphaFn_ne_const_ae (y t₁)).mono fun t₂ ht₂ => Ne.symm ht₂
  obtain ⟨M, hM1, hzM, hvand⟩ := vandermonde_log_bound hf hd
  let L : ℝ := min a b
  have hL_gt : (3.3 : ℝ) < L := lt_min ha_gt hb_gt
  have hL_pos : 0 < L := by linarith
  have hae_phi_ne : ∀ᵐ z ∂(nuProd.prod nuProd), phi z.1 ≠ phi z.2 := by
    have hm_ne : MeasurableSet {z : (Bool × ℝ) × (Bool × ℝ) | phi z.1 ≠ phi z.2} :=
      (((hm_phi.comp measurable_fst).prodMk (hm_phi.comp measurable_snd)) isClosed_diagonal.measurableSet).compl
    rw [ae_nuProd_prod_iff hm_ne]
    intro b₁ b₂
    cases b₁ <;> cases b₂
    · filter_upwards [hae_Ioo_prod, hae_alpha_diff] with pr hIoo hne
      intro heq
      have heq' : p pr.1 = p pr.2 := heq
      have hsub := hlip_pp_re pr.1 hIoo.1 pr.2 hIoo.2
      rw [heq', sub_self, abs_zero] at hsub
      have h0 : |alphaFn pr.1 - alphaFn pr.2| ≤ 0 := nonpos_of_mul_nonpos_right hsub ha0
      exact hne (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))))
    · filter_upwards [hae_Ioo_prod, hae_alpha_u] with pr hIoo hne
      intro heq
      have heq' : p pr.1 = q pr.2 := heq
      have hsub := hlip_pq_re pr.1 hIoo.1 pr.2
      rw [heq', sub_self, abs_zero] at hsub
      have h0 : |alphaFn pr.1 - u pr.2| ≤ 0 := nonpos_of_mul_nonpos_right hsub ha0
      exact hne (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))))
    · have hs := (Measure.measurePreserving_swap : MeasurePreserving Prod.swap (lam0.prod lam0) (lam0.prod lam0)).quasiMeasurePreserving.ae
        (hae_Ioo_prod.and hae_alpha_u)
      filter_upwards [hs] with pr ⟨hIoo, hne⟩
      dsimp only [Prod.swap] at hIoo hne
      intro heq
      have heq' : q pr.1 = p pr.2 := heq
      have hsub := hlip_pq_re pr.2 hIoo.1 pr.1
      rw [← heq', sub_self, abs_zero] at hsub
      have h0 : |alphaFn pr.2 - u pr.1| ≤ 0 := nonpos_of_mul_nonpos_right hsub ha0
      exact hne (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))))
    · filter_upwards [hae_Ioo_prod, hae_alpha_diff] with pr hIoo hne
      intro heq
      have heq' : q pr.1 = q pr.2 := heq
      have hsub := hlip_qq_im pr.1 hIoo.1 pr.2 hIoo.2
      rw [heq', sub_self, abs_zero] at hsub
      have h0 : |alphaFn pr.1 - alphaFn pr.2| ≤ 0 := nonpos_of_mul_nonpos_right hsub hb0
      exact hne (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))))
  have hint_log_phi : Integrable (fun z : (Bool × ℝ) × (Bool × ℝ) => Real.log ‖phi z.1 - phi z.2‖)
      (nuProd.prod nuProd) := by
    have hm_f : Measurable (fun z : (Bool × ℝ) × (Bool × ℝ) => Real.log ‖phi z.1 - phi z.2‖) :=
      Real.measurable_log.comp (continuous_norm.measurable.comp ((hm_phi.comp measurable_fst).sub (hm_phi.comp measurable_snd)))
    rw [integrable_nuProd_prod_iff hm_f]
    have hbd_fn : ∀ (b₁ b₂ : Bool) (dlt : ℝ × ℝ → ℝ),
        Integrable (fun p : ℝ × ℝ => Real.log (dlt p)) (lam0.prod lam0) →
        (∀ᵐ p : ℝ × ℝ ∂(lam0.prod lam0), L * dlt p ≤ ‖phi (b₁, p.1) - phi (b₂, p.2)‖ ∧ 0 < dlt p) →
        Integrable (fun p : ℝ × ℝ => Real.log ‖phi (b₁, p.1) - phi (b₂, p.2)‖) (lam0.prod lam0) := by
      intro b₁ b₂ dlt hdlt hcmp
      let bound : ℝ × ℝ → ℝ := fun pr => max |Real.log L| (Real.log (2 * M + 1)) + |Real.log (dlt pr)|
      have hbd_int : Integrable bound (lam0.prod lam0) :=
        (integrable_const _).add hdlt.abs
      refine hbd_int.mono ((hm_f.comp ((measurable_const.prodMk measurable_fst).prodMk (measurable_const.prodMk measurable_snd))).aestronglyMeasurable) ?_
      filter_upwards [hcmp] with pr ⟨hlow, hpos⟩
      have hup : ‖phi (b₁, pr.1) - phi (b₂, pr.2)‖ ≤ 2 * M + 1 := by
        have h1 := hzM _ (hphi_mem (b₁, pr.1))
        have h2 := hzM _ (hphi_mem (b₂, pr.2))
        calc ‖phi (b₁, pr.1) - phi (b₂, pr.2)‖
            ≤ ‖phi (b₁, pr.1)‖ + ‖phi (b₂, pr.2)‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add h1 h2
          _ ≤ 2 * M + 1 := by linarith
      have hnorm_pos : 0 < ‖phi (b₁, pr.1) - phi (b₂, pr.2)‖ :=
        lt_of_lt_of_le (mul_pos hL_pos hpos) hlow
      have hlo_log : Real.log L + Real.log (dlt pr) ≤ Real.log ‖phi (b₁, pr.1) - phi (b₂, pr.2)‖ := by
        rw [← Real.log_mul hL_pos.ne' hpos.ne']
        exact Real.log_le_log (mul_pos hL_pos hpos) hlow
      have hup_log : Real.log ‖phi (b₁, pr.1) - phi (b₂, pr.2)‖ ≤ Real.log (2 * M + 1) :=
        Real.log_le_log hnorm_pos hup
      have hbound_nonneg : 0 ≤ bound pr :=
        add_nonneg (le_max_of_le_left (abs_nonneg _)) (abs_nonneg _)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hbound_nonneg, abs_le]
      dsimp only [bound]
      have ha1 := le_abs_self (Real.log (dlt pr))
      have ha2 := neg_abs_le (Real.log (dlt pr))
      have hm1 := le_max_left |Real.log L| (Real.log (2 * M + 1))
      have hm2 := le_max_right |Real.log L| (Real.log (2 * M + 1))
      have hla := neg_abs_le (Real.log L)
      refine ⟨?_, ?_⟩ <;> linarith [abs_nonneg (Real.log (dlt pr))]
    have h_aa := integrable_and_integral_log_alpha_sub_fn hcont_alpha.measurable alphaFn_mem_Icc
    have h_au := integrable_and_integral_log_alpha_sub_fn hm_u hu_mem
    have h_ua : Integrable (fun pr : ℝ × ℝ => Real.log |alphaFn pr.2 - u pr.1|) (lam0.prod lam0) :=
      (Measure.measurePreserving_swap : MeasurePreserving Prod.swap (lam0.prod lam0) (lam0.prod lam0)).integrable_comp_emb
        MeasurableEquiv.prodComm.measurableEmbedding |>.mpr h_au.1
    intro b₁ b₂
    cases b₁ <;> cases b₂
    · refine hbd_fn false false (fun pr => |alphaFn pr.1 - alphaFn pr.2|) h_aa.1 ?_
      filter_upwards [hae_Ioo_prod, hae_alpha_diff] with pr hIoo hne
      refine ⟨?_, abs_pos.mpr (sub_ne_zero.mpr hne)⟩
      have h1 := hlip_pp_re pr.1 hIoo.1 pr.2 hIoo.2
      have h2 : L * |alphaFn pr.1 - alphaFn pr.2| ≤ a * |alphaFn pr.1 - alphaFn pr.2| :=
        mul_le_mul_of_nonneg_right (min_le_left a b) (abs_nonneg _)
      exact le_trans (le_trans h2 h1) (Complex.abs_re_le_norm (p pr.1 - p pr.2))
    · refine hbd_fn false true (fun pr => |alphaFn pr.1 - u pr.2|) h_au.1 ?_
      filter_upwards [hae_Ioo_prod, hae_alpha_u] with pr hIoo hne
      refine ⟨?_, abs_pos.mpr (sub_ne_zero.mpr hne)⟩
      have h1 := hlip_pq_re pr.1 hIoo.1 pr.2
      have h2 : L * |alphaFn pr.1 - u pr.2| ≤ a * |alphaFn pr.1 - u pr.2| :=
        mul_le_mul_of_nonneg_right (min_le_left a b) (abs_nonneg _)
      exact le_trans (le_trans h2 h1) (Complex.abs_re_le_norm (p pr.1 - q pr.2))
    · refine hbd_fn true false (fun pr => |alphaFn pr.2 - u pr.1|) h_ua ?_
      have hs := (Measure.measurePreserving_swap : MeasurePreserving Prod.swap (lam0.prod lam0) (lam0.prod lam0)).quasiMeasurePreserving.ae
        (hae_Ioo_prod.and hae_alpha_u)
      filter_upwards [hs] with pr ⟨hIoo, hne⟩
      dsimp only [Prod.swap] at hIoo hne
      refine ⟨?_, abs_pos.mpr (sub_ne_zero.mpr hne)⟩
      have h1 := hlip_pq_re pr.2 hIoo.1 pr.1
      have h2 : L * |alphaFn pr.2 - u pr.1| ≤ a * |alphaFn pr.2 - u pr.1| :=
        mul_le_mul_of_nonneg_right (min_le_left a b) (abs_nonneg _)
      have h3 : |(p pr.2).re - (q pr.1).re| = |(q pr.1).re - (p pr.2).re| := abs_sub_comm _ _
      rw [h3] at h1
      exact le_trans (le_trans h2 h1) (Complex.abs_re_le_norm (q pr.1 - p pr.2))
    · refine hbd_fn true true (fun pr => |alphaFn pr.1 - alphaFn pr.2|) h_aa.1 ?_
      filter_upwards [hae_Ioo_prod, hae_alpha_diff] with pr hIoo hne
      refine ⟨?_, abs_pos.mpr (sub_ne_zero.mpr hne)⟩
      have h1 := hlip_qq_im pr.1 hIoo.1 pr.2 hIoo.2
      have h2 : L * |alphaFn pr.1 - alphaFn pr.2| ≤ b * |alphaFn pr.1 - alphaFn pr.2| :=
        mul_le_mul_of_nonneg_right (min_le_right a b) (abs_nonneg _)
      exact le_trans (le_trans h2 h1) (Complex.abs_im_le_norm (q pr.1 - q pr.2))
  let I : ℝ := ∫ z : (Bool × ℝ) × (Bool × ℝ), Real.log ‖phi z.1 - phi z.2‖ ∂(nuProd.prod nuProd)
  have hI_nonpos : I ≤ 0 := by
    have h_avg : ∀ n : ℕ, 2 ≤ n →
        ((n : ℝ) * ((n : ℝ) - 1) / 2) * I ≤
          (n : ℝ) * Real.log (n : ℝ) + (f.natDegree : ℝ) * (n : ℝ) * Real.log M := by
      intro n hn
      let μn : Measure (Fin n → Bool × ℝ) := Measure.pi fun _ : Fin n => nuProd
      have hae_inj : ∀ᵐ ω ∂μn, Function.Injective (fun i : Fin n => phi (ω i)) := by
        have hpair_ae : ∀ (i j : Fin n), i ≠ j → ∀ᵐ ω ∂μn, phi (ω i) ≠ phi (ω j) := fun i j hij =>
          (measurePreserving_pair i j hij).quasiMeasurePreserving.ae hae_phi_ne
        have hall : ∀ᵐ ω ∂μn, ∀ i j : Fin n, i ≠ j → phi (ω i) ≠ phi (ω j) := by
          rw [ae_all_iff]
          intro i
          rw [ae_all_iff]
          intro j
          by_cases hij : i = j
          · subst hij; exact ae_of_all _ fun _ h => absurd rfl h
          · exact ae_all_iff.mpr fun _ => hpair_ae i j hij
        exact hall.mono fun ω hω i j hij => by
          by_contra hij_ne
          exact hω i j hij_ne hij
      have hpt : ∀ᵐ ω ∂μn,
          ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Real.log ‖phi (ω j) - phi (ω i)‖ ≤
            (n : ℝ) * Real.log (n : ℝ) + (f.natDegree : ℝ) * (n : ℝ) * Real.log M :=
        hae_inj.mono fun ω hinj => hvand n hn (fun i => phi (ω i)) (fun i => hphi_mem (ω i)) hinj
      have hm_pair : ∀ (i j : Fin n),
          Integrable (fun ω : Fin n → Bool × ℝ => Real.log ‖phi (ω j) - phi (ω i)‖) μn := fun i j => by
        by_cases hij : i = j
        · subst hij; simp [sub_self]
        · have hmp := measurePreserving_pair i j hij
          have hm_log : Measurable (fun z : (Bool × ℝ) × (Bool × ℝ) => Real.log ‖phi z.1 - phi z.2‖) :=
            Real.measurable_log.comp (continuous_norm.measurable.comp ((hm_phi.comp measurable_fst).sub (hm_phi.comp measurable_snd)))
          have hi2 : Integrable (fun z : (Bool × ℝ) × (Bool × ℝ) => Real.log ‖phi z.1 - phi z.2‖)
              (Measure.map (fun ω : Fin n → Bool × ℝ => (ω i, ω j)) μn) := by
            rw [hmp.map_eq]; exact hint_log_phi
          have hi3 := (integrable_map_measure hm_log.aestronglyMeasurable hmp.measurable.aemeasurable).mp hi2
          refine hi3.congr (ae_of_all _ fun ω => ?_)
          dsimp [Function.comp_def]
          rw [norm_sub_rev]
      have hsum_int : Integrable
          (fun ω : Fin n → Bool × ℝ => ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Real.log ‖phi (ω j) - phi (ω i)‖) μn :=
        integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hm_pair i j
      have hint_le := integral_mono_ae hsum_int (integrable_const _) hpt
      rw [integral_const, probReal_univ, one_smul, integral_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j _ => hm_pair i j] at hint_le
      have hterm : ∀ (i : Fin n) (j : Fin n), i < j →
          (∫ ω : Fin n → Bool × ℝ, Real.log ‖phi (ω j) - phi (ω i)‖ ∂μn) = I := by
        intro i j hij_lt
        have hij : i ≠ j := ne_of_lt hij_lt
        have hmp := measurePreserving_pair i j hij
        have hm_log : Measurable (fun z : (Bool × ℝ) × (Bool × ℝ) => Real.log ‖phi z.1 - phi z.2‖) :=
          Real.measurable_log.comp (continuous_norm.measurable.comp ((hm_phi.comp measurable_fst).sub (hm_phi.comp measurable_snd)))
        have him_eq := integral_map (φ := fun ω : Fin n → Bool × ℝ => (ω i, ω j))
          hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hm_log.aestronglyMeasurable)
          (f := fun z : (Bool × ℝ) × (Bool × ℝ) => Real.log ‖phi z.1 - phi z.2‖)
        rw [hmp.map_eq] at him_eq
        calc (∫ ω : Fin n → Bool × ℝ, Real.log ‖phi (ω j) - phi (ω i)‖ ∂μn)
            = ∫ ω : Fin n → Bool × ℝ, Real.log ‖phi (ω i) - phi (ω j)‖ ∂μn := by
              refine integral_congr_ae (ae_of_all _ fun ω => by dsimp only; rw [norm_sub_rev])
          _ = I := him_eq.symm
      have hlhs : ∑ i : Fin n, (∫ ω : Fin n → Bool × ℝ, ∑ j ∈ Finset.Ioi i, Real.log ‖phi (ω j) - phi (ω i)‖ ∂μn) =
          ((n : ℝ) * ((n : ℝ) - 1) / 2) * I := by
        calc ∑ i : Fin n, (∫ ω : Fin n → Bool × ℝ, ∑ j ∈ Finset.Ioi i, Real.log ‖phi (ω j) - phi (ω i)‖ ∂μn)
            = ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (∫ ω : Fin n → Bool × ℝ, Real.log ‖phi (ω j) - phi (ω i)‖ ∂μn) := by
              refine Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hm_pair i j
          _ = ∑ i : Fin n, ∑ _j ∈ Finset.Ioi i, I := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
                hterm i j (Finset.mem_Ioi.mp hj)
          _ = (∑ i : Fin n, ((Finset.Ioi i).card : ℝ)) * I := by
              simp [Finset.sum_const, nsmul_eq_mul, Finset.sum_mul]
          _ = ((n : ℝ) * ((n : ℝ) - 1) / 2) * I := by rw [card_Ioi_sum]
      rw [hlhs] at hint_le
      exact hint_le
    by_contra hpos
    push Not at hpos
    obtain ⟨k, hk⟩ := exists_nat_gt ((8 + 4 * max 0 ((f.natDegree : ℝ) * Real.log M)) / I + 2)
    have hk2 : 2 ≤ k := by
      have : (2 : ℝ) ≤ (8 + 4 * max 0 ((f.natDegree : ℝ) * Real.log M)) / I + 2 := by
        have : 0 ≤ (8 + 4 * max 0 ((f.natDegree : ℝ) * Real.log M)) / I := by positivity
        linarith
      exact_mod_cast le_of_lt (lt_of_le_of_lt this hk)
    let n : ℕ := k * k
    have hn2 : 2 ≤ n := Nat.le_trans (by norm_num : 2 ≤ 2 * 2) (Nat.mul_le_mul hk2 hk2)
    have hav := h_avg n hn2
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by dsimp [n]; nlinarith : 0 < n)
    have hlog_bd : Real.log (n : ℝ) ≤ 2 * (k : ℝ) := by
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hsq : (n : ℝ) = (k : ℝ) ^ 2 := by dsimp [n]; push_cast; ring
      rw [hsq, Real.log_pow]
      push_cast
      have h1 := Real.log_le_sub_one_of_pos hkpos
      linarith
    have hdiv : ((n : ℝ) - 1) / 2 * I ≤ Real.log (n : ℝ) + (f.natDegree : ℝ) * Real.log M := by
      have hmul : (n : ℝ) * (((n : ℝ) - 1) / 2 * I) ≤
          (n : ℝ) * (Real.log (n : ℝ) + (f.natDegree : ℝ) * Real.log M) := by
        calc (n : ℝ) * (((n : ℝ) - 1) / 2 * I)
            = ((n : ℝ) * ((n : ℝ) - 1) / 2) * I := by ring
          _ ≤ (n : ℝ) * Real.log (n : ℝ) + (f.natDegree : ℝ) * (n : ℝ) * Real.log M := hav
          _ = (n : ℝ) * (Real.log (n : ℝ) + (f.natDegree : ℝ) * Real.log M) := by ring
      exact le_of_mul_le_mul_left hmul hn_pos
    have hk_r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hn_r : (n : ℝ) = (k : ℝ) * k := by dsimp [n]; push_cast; ring
    have hge_half : (k : ℝ) * k / 2 ≤ (n : ℝ) - 1 := by
      rw [hn_r]; nlinarith
    have h1 : ((k : ℝ) * k / 4) * I ≤ 2 * (k : ℝ) + max 0 ((f.natDegree : ℝ) * Real.log M) := by
      have h1' : (k : ℝ) * k / 4 * I ≤ ((n : ℝ) - 1) / 2 * I := by nlinarith
      linarith [le_max_right 0 ((f.natDegree : ℝ) * Real.log M)]
    have hkgt : (k : ℝ) * I > 8 + 4 * max 0 ((f.natDegree : ℝ) * Real.log M) := by
      have hk1 : (8 + 4 * max 0 ((f.natDegree : ℝ) * Real.log M)) / I < k := by linarith
      exact (div_lt_iff₀ hpos).mp hk1
    have hmax0 : 0 ≤ 4 * max 0 ((f.natDegree : ℝ) * Real.log M) := by positivity
    nlinarith
  have hlog_sq_norm : ∀ z₁ z₂ : ℂ, z₁ ≠ z₂ →
      Real.log ‖z₁ - z₂‖ = (1 / 2 : ℝ) * Real.log ((z₁.re - z₂.re) ^ 2 + (z₁.im - z₂.im) ^ 2) := by
    intro z₁ z₂ hne
    have hsq : ‖z₁ - z₂‖ ^ 2 = (z₁.re - z₂.re) ^ 2 + (z₁.im - z₂.im) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im]
      ring
    rw [← hsq, Real.log_pow]
    ring
  have hm_y_int := integrable_and_integral_log_alpha_sub_fn hcont_alpha.measurable alphaFn_mem_Icc
  have hm_u_int := integrable_and_integral_log_alpha_sub_fn hm_u hu_mem
  have hm_e1_y : Integrable (fun pr : ℝ × ℝ => e1Rat (alphaFn pr.1) (y pr.1) (alphaFn pr.2) (y pr.2)) (lam0.prod lam0) := by
    refine (integrable_const (1 : ℝ)).mono ?_ (ae_of_all _ fun pr => ?_)
    · unfold e1Rat
      have hm1 : Measurable (fun pr : ℝ × ℝ => (alphaFn pr.1 - alphaFn pr.2)) :=
        (hcont_alpha.measurable.comp measurable_fst).sub (hcont_alpha.measurable.comp measurable_snd)
      have hm2 : Measurable (fun pr : ℝ × ℝ => (y pr.1 - y pr.2)) :=
        (hm_y.comp measurable_fst).sub (hm_y.comp measurable_snd)
      exact (Measurable.ite (hm1 (measurableSet_singleton 0)) measurable_const
        (((hm2.pow_const 2).div (hm1.pow_const 2)).div (measurable_const.add ((hm2.pow_const 2).div (hm1.pow_const 2))))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (e1Rat_bounds _ _ _ _).1, norm_one]
      exact (e1Rat_bounds _ _ _ _).2
  have hm_e1_u : Integrable (fun pr : ℝ × ℝ => e1Rat (alphaFn pr.1) (u pr.1) (alphaFn pr.2) (u pr.2)) (lam0.prod lam0) := by
    refine (integrable_const (1 : ℝ)).mono ?_ (ae_of_all _ fun pr => ?_)
    · unfold e1Rat
      have hm1 : Measurable (fun pr : ℝ × ℝ => (alphaFn pr.1 - alphaFn pr.2)) :=
        (hcont_alpha.measurable.comp measurable_fst).sub (hcont_alpha.measurable.comp measurable_snd)
      have hm2 : Measurable (fun pr : ℝ × ℝ => (u pr.1 - u pr.2)) :=
        (hm_u.comp measurable_fst).sub (hm_u.comp measurable_snd)
      exact (Measurable.ite (hm1 (measurableSet_singleton 0)) measurable_const
        (((hm2.pow_const 2).div (hm1.pow_const 2)).div (measurable_const.add ((hm2.pow_const 2).div (hm1.pow_const 2))))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (e1Rat_bounds _ _ _ _).1, norm_one]
      exact (e1Rat_bounds _ _ _ _).2
  have hm_e12 : Integrable (fun pr : ℝ × ℝ => e12Rat (alphaFn pr.1) (y pr.1) (u pr.2) (alphaFn pr.2)) (lam0.prod lam0) := by
    refine (integrable_const (1 : ℝ)).mono ?_ (ae_of_all _ fun pr => ?_)
    · unfold e12Rat
      have hm1 : Measurable (fun pr : ℝ × ℝ => |alphaFn pr.1 - u pr.2|) :=
        continuous_abs.measurable.comp ((hcont_alpha.measurable.comp measurable_fst).sub (hm_u.comp measurable_snd))
      have hm2 : Measurable (fun pr : ℝ × ℝ => |y pr.1 - alphaFn pr.2|) :=
        continuous_abs.measurable.comp ((hm_y.comp measurable_fst).sub (hcont_alpha.measurable.comp measurable_snd))
      exact (Measurable.ite ((hm1 (measurableSet_singleton 0)).union (hm2 (measurableSet_singleton 0))) measurable_const
        (((hm1.sub hm2).div (hm1.add hm2)).pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (e12Rat_bounds _ _ _ _).1, norm_one]
      exact (e12Rat_bounds _ _ _ _).2
  have hI_exp := integral_nuProd_prod hint_log_phi
  have hLogPhi_parts := (integrable_nuProd_prod_iff (Real.measurable_log.comp (continuous_norm.measurable.comp
    ((hm_phi.comp measurable_fst).sub (hm_phi.comp measurable_snd))))).mp hint_log_phi
  have hFF_int : Integrable (fun p : ℝ × ℝ => Real.log ‖phi (false, p.1) - phi (false, p.2)‖) (lam0.prod lam0) :=
    hLogPhi_parts false false
  have hFT_int : Integrable (fun p : ℝ × ℝ => Real.log ‖phi (false, p.1) - phi (true, p.2)‖) (lam0.prod lam0) :=
    hLogPhi_parts false true
  have hTT_int : Integrable (fun p : ℝ × ℝ => Real.log ‖phi (true, p.1) - phi (true, p.2)‖) (lam0.prod lam0) :=
    hLogPhi_parts true true
  have hFF_le : Real.log L - 2 * Real.log 2 +
      (∫ pr : ℝ × ℝ, e1Rat (alphaFn pr.1) (y pr.1) (alphaFn pr.2) (y pr.2) ∂(lam0.prod lam0)) ≤
      ∫ pr : ℝ × ℝ, Real.log ‖phi (false, pr.1) - phi (false, pr.2)‖ ∂(lam0.prod lam0) := by
    have hpt : ∀ᵐ pr : ℝ × ℝ ∂(lam0.prod lam0),
        Real.log L + Real.log |alphaFn pr.1 - alphaFn pr.2| +
          e1Rat (alphaFn pr.1) (y pr.1) (alphaFn pr.2) (y pr.2) ≤
        Real.log ‖phi (false, pr.1) - phi (false, pr.2)‖ := by
      filter_upwards [hae_Ioo_prod, hae_alpha_diff] with pr hIoo hne
      have h1 := hlip_pp_re pr.1 hIoo.1 pr.2 hIoo.2
      have h2 := hlip_y pr.1 pr.2
      have hd1 : L * |alphaFn pr.1 - alphaFn pr.2| ≤ |(p pr.1).re - (p pr.2).re| :=
        le_trans (mul_le_mul_of_nonneg_right (min_le_left a b) (abs_nonneg _)) h1
      have hd2 : L * |y pr.1 - y pr.2| ≤ |(p pr.1).im - (p pr.2).im| :=
        le_trans (mul_le_mul_of_nonneg_right (min_le_right a b) (abs_nonneg _)) h2
      have hsq : L ^ 2 * ((alphaFn pr.1 - alphaFn pr.2) ^ 2 + (y pr.1 - y pr.2) ^ 2) ≤
          ((p pr.1).re - (p pr.2).re) ^ 2 + ((p pr.1).im - (p pr.2).im) ^ 2 := by
        have hs1 : L ^ 2 * (alphaFn pr.1 - alphaFn pr.2) ^ 2 ≤ ((p pr.1).re - (p pr.2).re) ^ 2 := by
          simpa [mul_pow, sq_abs] using pow_le_pow_left₀ (mul_nonneg hL_pos.le (abs_nonneg _)) hd1 2
        have hs2 : L ^ 2 * (y pr.1 - y pr.2) ^ 2 ≤ ((p pr.1).im - (p pr.2).im) ^ 2 := by
          simpa [mul_pow, sq_abs] using pow_le_pow_left₀ (mul_nonneg hL_pos.le (abs_nonneg _)) hd2 2
        linarith
      have hda_ne : alphaFn pr.1 - alphaFn pr.2 ≠ 0 := sub_ne_zero.mpr hne
      have hp_ne : phi (false, pr.1) ≠ phi (false, pr.2) := fun he => by
        have he' : p pr.1 = p pr.2 := he
        rw [he', sub_self, abs_zero] at hd1
        have h0 : |alphaFn pr.1 - alphaFn pr.2| ≤ 0 := nonpos_of_mul_nonpos_right hd1 hL_pos
        exact hda_ne (abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _)))
      have hnorm_ge := hlog_sq_norm (phi (false, pr.1)) (phi (false, pr.2)) hp_ne
      have hlhs_pos : 0 < L ^ 2 * ((alphaFn pr.1 - alphaFn pr.2) ^ 2 + (y pr.1 - y pr.2) ^ 2) :=
        mul_pos (sq_pos_of_pos hL_pos) (by positivity)
      have hlog1 := Real.log_le_log hlhs_pos hsq
      have hfac : L ^ 2 * ((alphaFn pr.1 - alphaFn pr.2) ^ 2 + (y pr.1 - y pr.2) ^ 2) =
          (L * |alphaFn pr.1 - alphaFn pr.2|) ^ 2 *
            (1 + ((y pr.1 - y pr.2) / (alphaFn pr.1 - alphaFn pr.2)) ^ 2) := by
        rw [mul_pow, sq_abs]; field_simp [hda_ne]
      dsimp [phi, phiMap] at hnorm_ge ⊢
      rw [hnorm_ge]
      have hlog2 : (1 / 2 : ℝ) * Real.log (L ^ 2 * ((alphaFn pr.1 - alphaFn pr.2) ^ 2 + (y pr.1 - y pr.2) ^ 2)) ≤
          (1 / 2 : ℝ) * Real.log (((p pr.1).re - (p pr.2).re) ^ 2 + ((p pr.1).im - (p pr.2).im) ^ 2) := by
        linarith
      rw [hfac, Real.log_mul (pow_ne_zero 2 (mul_pos hL_pos (abs_pos.mpr hda_ne)).ne') (by positivity),
        Real.log_pow, Real.log_mul hL_pos.ne' (abs_pos.mpr hda_ne).ne'] at hlog2
      have hrat := half_log_one_add_sq_ge ((y pr.1 - y pr.2) / (alphaFn pr.1 - alphaFn pr.2))
      have herat : e1Rat (alphaFn pr.1) (y pr.1) (alphaFn pr.2) (y pr.2) =
          ((y pr.1 - y pr.2) / (alphaFn pr.1 - alphaFn pr.2)) ^ 2 /
            (2 + ((y pr.1 - y pr.2) / (alphaFn pr.1 - alphaFn pr.2)) ^ 2) := by
        unfold e1Rat; dsimp only; rw [if_neg hda_ne, div_pow]
      linarith
    have h12 : Integrable (fun pr : ℝ × ℝ => Real.log L + Real.log |alphaFn pr.1 - alphaFn pr.2|) (lam0.prod lam0) :=
      (integrable_const _).add hm_y_int.1
    have hint_lhs : Integrable (fun pr : ℝ × ℝ =>
        (Real.log L + Real.log |alphaFn pr.1 - alphaFn pr.2|) +
          e1Rat (alphaFn pr.1) (y pr.1) (alphaFn pr.2) (y pr.2)) (lam0.prod lam0) :=
      h12.add hm_e1_y
    have him := integral_mono_ae hint_lhs hFF_int hpt
    change (∫ pr : ℝ × ℝ, (Real.log L + Real.log |alphaFn pr.1 - alphaFn pr.2|) +
        e1Rat (alphaFn pr.1) (y pr.1) (alphaFn pr.2) (y pr.2) ∂(lam0.prod lam0)) ≤ _ at him
    rw [integral_add h12 hm_e1_y, integral_add (integrable_const _) hm_y_int.1,
      integral_const, probReal_univ, one_smul, hm_y_int.2] at him
    linarith
  have hTT_le : Real.log L - 2 * Real.log 2 +
      (∫ pr : ℝ × ℝ, e1Rat (alphaFn pr.1) (u pr.1) (alphaFn pr.2) (u pr.2) ∂(lam0.prod lam0)) ≤
      ∫ pr : ℝ × ℝ, Real.log ‖phi (true, pr.1) - phi (true, pr.2)‖ ∂(lam0.prod lam0) := by
    have hpt : ∀ᵐ pr : ℝ × ℝ ∂(lam0.prod lam0),
        Real.log L + Real.log |alphaFn pr.1 - alphaFn pr.2| +
          e1Rat (alphaFn pr.1) (u pr.1) (alphaFn pr.2) (u pr.2) ≤
        Real.log ‖phi (true, pr.1) - phi (true, pr.2)‖ := by
      filter_upwards [hae_Ioo_prod, hae_alpha_diff] with pr hIoo hne
      have h1 := hlip_u pr.1 pr.2
      have h2 := hlip_qq_im pr.1 hIoo.1 pr.2 hIoo.2
      have hd1 : L * |u pr.1 - u pr.2| ≤ |(q pr.1).re - (q pr.2).re| :=
        le_trans (mul_le_mul_of_nonneg_right (min_le_left a b) (abs_nonneg _)) h1
      have hd2 : L * |alphaFn pr.1 - alphaFn pr.2| ≤ |(q pr.1).im - (q pr.2).im| :=
        le_trans (mul_le_mul_of_nonneg_right (min_le_right a b) (abs_nonneg _)) h2
      have hsq : L ^ 2 * ((alphaFn pr.1 - alphaFn pr.2) ^ 2 + (u pr.1 - u pr.2) ^ 2) ≤
          ((q pr.1).re - (q pr.2).re) ^ 2 + ((q pr.1).im - (q pr.2).im) ^ 2 := by
        have hs1 : L ^ 2 * (u pr.1 - u pr.2) ^ 2 ≤ ((q pr.1).re - (q pr.2).re) ^ 2 := by
          simpa [mul_pow, sq_abs] using pow_le_pow_left₀ (mul_nonneg hL_pos.le (abs_nonneg _)) hd1 2
        have hs2 : L ^ 2 * (alphaFn pr.1 - alphaFn pr.2) ^ 2 ≤ ((q pr.1).im - (q pr.2).im) ^ 2 := by
          simpa [mul_pow, sq_abs] using pow_le_pow_left₀ (mul_nonneg hL_pos.le (abs_nonneg _)) hd2 2
        linarith
      have hda_ne : alphaFn pr.1 - alphaFn pr.2 ≠ 0 := sub_ne_zero.mpr hne
      have hp_ne : phi (true, pr.1) ≠ phi (true, pr.2) := fun he => by
        have he' : q pr.1 = q pr.2 := he
        rw [he', sub_self, abs_zero] at hd2
        have h0 : |alphaFn pr.1 - alphaFn pr.2| ≤ 0 := nonpos_of_mul_nonpos_right hd2 hL_pos
        exact hda_ne (abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _)))
      have hnorm_ge := hlog_sq_norm (phi (true, pr.1)) (phi (true, pr.2)) hp_ne
      have hlhs_pos : 0 < L ^ 2 * ((alphaFn pr.1 - alphaFn pr.2) ^ 2 + (u pr.1 - u pr.2) ^ 2) :=
        mul_pos (sq_pos_of_pos hL_pos) (by positivity)
      have hlog1 := Real.log_le_log hlhs_pos hsq
      have hfac : L ^ 2 * ((alphaFn pr.1 - alphaFn pr.2) ^ 2 + (u pr.1 - u pr.2) ^ 2) =
          (L * |alphaFn pr.1 - alphaFn pr.2|) ^ 2 *
            (1 + ((u pr.1 - u pr.2) / (alphaFn pr.1 - alphaFn pr.2)) ^ 2) := by
        rw [mul_pow, sq_abs]; field_simp [hda_ne]
      dsimp [phi, phiMap] at hnorm_ge ⊢
      rw [hnorm_ge]
      have hlog2 : (1 / 2 : ℝ) * Real.log (L ^ 2 * ((alphaFn pr.1 - alphaFn pr.2) ^ 2 + (u pr.1 - u pr.2) ^ 2)) ≤
          (1 / 2 : ℝ) * Real.log (((q pr.1).re - (q pr.2).re) ^ 2 + ((q pr.1).im - (q pr.2).im) ^ 2) := by
        linarith
      rw [hfac, Real.log_mul (pow_ne_zero 2 (mul_pos hL_pos (abs_pos.mpr hda_ne)).ne') (by positivity),
        Real.log_pow, Real.log_mul hL_pos.ne' (abs_pos.mpr hda_ne).ne'] at hlog2
      have hrat := half_log_one_add_sq_ge ((u pr.1 - u pr.2) / (alphaFn pr.1 - alphaFn pr.2))
      have herat : e1Rat (alphaFn pr.1) (u pr.1) (alphaFn pr.2) (u pr.2) =
          ((u pr.1 - u pr.2) / (alphaFn pr.1 - alphaFn pr.2)) ^ 2 /
            (2 + ((u pr.1 - u pr.2) / (alphaFn pr.1 - alphaFn pr.2)) ^ 2) := by
        unfold e1Rat; dsimp only; rw [if_neg hda_ne, div_pow]
      linarith
    have h12 : Integrable (fun pr : ℝ × ℝ => Real.log L + Real.log |alphaFn pr.1 - alphaFn pr.2|) (lam0.prod lam0) :=
      (integrable_const _).add hm_y_int.1
    have hint_lhs : Integrable (fun pr : ℝ × ℝ =>
        (Real.log L + Real.log |alphaFn pr.1 - alphaFn pr.2|) +
          e1Rat (alphaFn pr.1) (u pr.1) (alphaFn pr.2) (u pr.2)) (lam0.prod lam0) :=
      h12.add hm_e1_u
    have him := integral_mono_ae hint_lhs hTT_int hpt
    change (∫ pr : ℝ × ℝ, (Real.log L + Real.log |alphaFn pr.1 - alphaFn pr.2|) +
        e1Rat (alphaFn pr.1) (u pr.1) (alphaFn pr.2) (u pr.2) ∂(lam0.prod lam0)) ≤ _ at him
    rw [integral_add h12 hm_e1_u, integral_add (integrable_const _) hm_y_int.1,
      integral_const, probReal_univ, one_smul, hm_y_int.2] at him
    linarith
  have hFT_le : Real.log L + (1 / 2 : ℝ) * Real.log 2 - 2 * Real.log 2 +
      (∫ pr : ℝ × ℝ, e12Rat (alphaFn pr.1) (y pr.1) (u pr.2) (alphaFn pr.2) ∂(lam0.prod lam0)) ≤
      ∫ pr : ℝ × ℝ, Real.log ‖phi (false, pr.1) - phi (true, pr.2)‖ ∂(lam0.prod lam0) := by
    have hm_ya_swap : Integrable (fun pr : ℝ × ℝ => Real.log |y pr.1 - alphaFn pr.2|) (lam0.prod lam0) ∧
        (∫ pr : ℝ × ℝ, Real.log |y pr.1 - alphaFn pr.2| ∂(lam0.prod lam0)) = -2 * Real.log 2 := by
      have hsw := integrable_and_integral_log_alpha_sub_fn hm_y hy_mem
      have hmp : MeasurePreserving Prod.swap (lam0.prod lam0) (lam0.prod lam0) := Measure.measurePreserving_swap
      have h1 : Integrable (fun pr : ℝ × ℝ => Real.log |y pr.1 - alphaFn pr.2|) (lam0.prod lam0) := by
        refine ((hmp.integrable_comp_emb MeasurableEquiv.prodComm.measurableEmbedding).mpr hsw.1).congr ?_
        refine ae_of_all _ fun pr => ?_
        dsimp only [Function.comp_def, Prod.swap]
        rw [abs_sub_comm]
      have h2 : (∫ pr : ℝ × ℝ, Real.log |y pr.1 - alphaFn pr.2| ∂(lam0.prod lam0)) = -2 * Real.log 2 := by
        rw [← hsw.2, ← hmp.integral_comp MeasurableEquiv.prodComm.measurableEmbedding]
        refine integral_congr_ae (ae_of_all _ fun pr => ?_)
        dsimp only [Function.comp_def, Prod.swap]
        rw [abs_sub_comm]
      exact ⟨h1, h2⟩
    have hpt : ∀ᵐ pr : ℝ × ℝ ∂(lam0.prod lam0),
        Real.log L + (1 / 2 : ℝ) * Real.log 2 +
          (1 / 2 : ℝ) * Real.log |alphaFn pr.1 - u pr.2| +
          (1 / 2 : ℝ) * Real.log |y pr.1 - alphaFn pr.2| +
          e12Rat (alphaFn pr.1) (y pr.1) (u pr.2) (alphaFn pr.2) ≤
        Real.log ‖phi (false, pr.1) - phi (true, pr.2)‖ := by
      filter_upwards [hae_Ioo_prod, hae_alpha_u, hae_y_alpha] with pr hIoo hne1 hne2
      let A := |alphaFn pr.1 - u pr.2|
      let B := |y pr.1 - alphaFn pr.2|
      have hA : 0 < A := abs_pos.mpr (sub_ne_zero.mpr hne1)
      have hB : 0 < B := abs_pos.mpr (sub_ne_zero.mpr hne2)
      have hd1 : L * A ≤ |(p pr.1).re - (q pr.2).re| :=
        le_trans (mul_le_mul_of_nonneg_right (min_le_left a b) (abs_nonneg _)) (hlip_pq_re pr.1 hIoo.1 pr.2)
      have hd2 : L * B ≤ |(p pr.1).im - (q pr.2).im| :=
        le_trans (mul_le_mul_of_nonneg_right (min_le_right a b) (abs_nonneg _)) (hlip_pq_im pr.1 pr.2 hIoo.2)
      have hsq : L ^ 2 * (A ^ 2 + B ^ 2) ≤
          ((p pr.1).re - (q pr.2).re) ^ 2 + ((p pr.1).im - (q pr.2).im) ^ 2 := by
        have hs1 : L ^ 2 * A ^ 2 ≤ ((p pr.1).re - (q pr.2).re) ^ 2 := by
          simpa [mul_pow, sq_abs] using pow_le_pow_left₀ (mul_nonneg hL_pos.le hA.le) hd1 2
        have hs2 : L ^ 2 * B ^ 2 ≤ ((p pr.1).im - (q pr.2).im) ^ 2 := by
          simpa [mul_pow, sq_abs] using pow_le_pow_left₀ (mul_nonneg hL_pos.le hB.le) hd2 2
        linarith
      have hp_ne : phi (false, pr.1) ≠ phi (true, pr.2) := fun he => by
        have he' : p pr.1 = q pr.2 := he
        rw [he', sub_self, abs_zero] at hd1
        have h0 : A ≤ 0 := nonpos_of_mul_nonpos_right hd1 hL_pos
        linarith
      have hnorm_ge := hlog_sq_norm (phi (false, pr.1)) (phi (true, pr.2)) hp_ne
      have hlhs_pos : 0 < L ^ 2 * (A ^ 2 + B ^ 2) := mul_pos (sq_pos_of_pos hL_pos) (by positivity)
      have hlog1 := Real.log_le_log hlhs_pos hsq
      have hfac : L ^ 2 * (A ^ 2 + B ^ 2) =
          (L ^ 2 * (2 * A * B)) * ((A ^ 2 + B ^ 2) / (2 * A * B)) := by
        field_simp [hA.ne', hB.ne']
      dsimp [phi, phiMap] at hnorm_ge ⊢
      rw [hnorm_ge]
      have hlog2 : (1 / 2 : ℝ) * Real.log (L ^ 2 * (A ^ 2 + B ^ 2)) ≤
          (1 / 2 : ℝ) * Real.log (((p pr.1).re - (q pr.2).re) ^ 2 + ((p pr.1).im - (q pr.2).im) ^ 2) := by
        linarith
      rw [hfac, Real.log_mul (mul_pos (sq_pos_of_pos hL_pos) (by positivity)).ne' (by positivity),
        Real.log_mul (sq_pos_of_pos hL_pos).ne' (by positivity),
        Real.log_mul (by positivity) hB.ne', Real.log_mul (by norm_num) hA.ne', Real.log_pow] at hlog2
      have hrat := half_log_amgm_ge hA hB
      have herat : e12Rat (alphaFn pr.1) (y pr.1) (u pr.2) (alphaFn pr.2) = ((A - B) / (A + B)) ^ 2 := by
        unfold e12Rat; dsimp only; rw [if_neg (not_or.mpr ⟨hA.ne', hB.ne'⟩)]
      linarith
    have h1 : Integrable (fun pr : ℝ × ℝ => Real.log L + (1 / 2 : ℝ) * Real.log 2) (lam0.prod lam0) :=
      integrable_const _
    have h2 : Integrable (fun pr : ℝ × ℝ =>
        (Real.log L + (1 / 2 : ℝ) * Real.log 2) + (1 / 2 : ℝ) * Real.log |alphaFn pr.1 - u pr.2|) (lam0.prod lam0) :=
      h1.add (hm_u_int.1.const_mul _)
    have h123 : Integrable (fun pr : ℝ × ℝ =>
        ((Real.log L + (1 / 2 : ℝ) * Real.log 2) + (1 / 2 : ℝ) * Real.log |alphaFn pr.1 - u pr.2|) +
          (1 / 2 : ℝ) * Real.log |y pr.1 - alphaFn pr.2|) (lam0.prod lam0) :=
      h2.add (hm_ya_swap.1.const_mul _)
    have hint_lhs : Integrable (fun pr : ℝ × ℝ =>
        (((Real.log L + (1 / 2 : ℝ) * Real.log 2) + (1 / 2 : ℝ) * Real.log |alphaFn pr.1 - u pr.2|) +
          (1 / 2 : ℝ) * Real.log |y pr.1 - alphaFn pr.2|) +
          e12Rat (alphaFn pr.1) (y pr.1) (u pr.2) (alphaFn pr.2)) (lam0.prod lam0) :=
      h123.add hm_e12
    have him := integral_mono_ae hint_lhs hFT_int hpt
    change (∫ pr : ℝ × ℝ, (((Real.log L + (1 / 2 : ℝ) * Real.log 2) +
        (1 / 2 : ℝ) * Real.log |alphaFn pr.1 - u pr.2|) +
        (1 / 2 : ℝ) * Real.log |y pr.1 - alphaFn pr.2|) +
        e12Rat (alphaFn pr.1) (y pr.1) (u pr.2) (alphaFn pr.2) ∂(lam0.prod lam0)) ≤ _ at him
    rw [integral_add h123 hm_e12, integral_add h2 (hm_ya_swap.1.const_mul _),
      integral_add h1 (hm_u_int.1.const_mul _),
      integral_const, probReal_univ, one_smul,
      integral_const_mul, integral_const_mul, hm_u_int.2, hm_ya_swap.2] at him
    linarith
  have hTF_eq : (∫ pr : ℝ × ℝ, Real.log ‖phi (true, pr.1) - phi (false, pr.2)‖ ∂(lam0.prod lam0)) =
      ∫ pr : ℝ × ℝ, Real.log ‖phi (false, pr.1) - phi (true, pr.2)‖ ∂(lam0.prod lam0) := by
    have hmp : MeasurePreserving Prod.swap (lam0.prod lam0) (lam0.prod lam0) := Measure.measurePreserving_swap
    rw [← hmp.integral_comp MeasurableEquiv.prodComm.measurableEmbedding]
    refine integral_congr_ae (ae_of_all _ fun pr => ?_)
    dsimp only [Function.comp_def, Prod.swap]
    rw [norm_sub_rev]
  have hE_log : energyRat y u ≤ 2 * Real.log 2 - (1 / 4 : ℝ) * Real.log 2 - Real.log L := by
    unfold energyRat
    linarith
  have hL_log : Real.log (33 / 10 : ℝ) < Real.log L :=
    Real.log_lt_log (by norm_num) (by linarith)
  have hcomb : (7 / 4 : ℝ) * Real.log 2 - Real.log (33 / 10 : ℝ) =
      (1 / 4 : ℝ) * Real.log (1280000 / 1185921 : ℝ) := by
    have hpow2 : Real.log ((2 : ℝ) ^ 7) = 7 * Real.log 2 := by rw [Real.log_pow]; norm_num
    have hpow3 : Real.log ((33 / 10 : ℝ) ^ 4) = 4 * Real.log (33 / 10 : ℝ) := by rw [Real.log_pow]; norm_num
    have hdiv : Real.log (1280000 / 1185921 : ℝ) = Real.log ((2 : ℝ) ^ 7) - Real.log ((33 / 10 : ℝ) ^ 4) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      congr 1; norm_num
    rw [hdiv, hpow2, hpow3]
    ring
  have hlog_ub : Real.log (1280000 / 1185921 : ℝ) ≤ 94079 / 1185921 := by
    have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1280000 / 1185921)
    linarith
  refine ⟨z₀, hz₀, hy_mem, hu_mem, hm_y, hm_u, ?_⟩
  linarith

-- ============================================================================
-- Section 6A: 14-bucket discretization lower bound on energyRat
-- ============================================================================

private def wxList : List ℤ := [188, 79, 62, 53, 47, 40, 31, 31, 40, 47, 53, 62, 79, 188]
private def tNumList : List ℕ := [0, 188, 267, 329, 382, 429, 469, 500, 531, 571, 618, 671, 733, 812, 1000]
private def exLoList : List ℤ := [0, 846, 1657, 2440, 3188, 3893, 4513, 5000, 5485, 6105, 6810, 7558, 8341, 9152, 10000]
private def exHiList : List ℤ := [0, 848, 1659, 2442, 3190, 3895, 4515, 5000, 5487, 6107, 6812, 7560, 8343, 9154, 10000]
private def eyList : List ℤ := [0, 850, 1660, 2440, 3190, 3890, 4510, 5000, 5490, 6110, 6810, 7560, 8340, 9150, 10000]

private def getAt (xs : List ℤ) (k : ℕ) : ℤ :=
  match xs, k with
  | x :: _, 0 => x
  | _ :: xs, k + 1 => getAt xs k
  | [], _ => 0

private def getAtNat (xs : List ℕ) (k : ℕ) : ℕ :=
  match xs, k with
  | x :: _, 0 => x
  | _ :: xs, k + 1 => getAtNat xs k
  | [], _ => 0

private def distIv (alo ahi blo bhi : ℤ) : ℤ :=
  if ahi ≥ blo ∧ bhi ≥ alo then 0
  else if ahi < blo then blo - ahi else alo - bhi

private def maxdistIv (alo ahi blo bhi : ℤ) : ℤ :=
  let d1 := Int.natAbs (alo - bhi)
  let d2 := Int.natAbs (ahi - blo)
  Int.ofNat (if d1 ≥ d2 then d1 else d2)

private def M1Int (i j i2 j2 : ℕ) : ℤ :=
  let ylo := getAt eyList j
  let yhi := getAt eyList (j + 1)
  let y2lo := getAt eyList j2
  let y2hi := getAt eyList (j2 + 1)
  let dy := distIv ylo yhi y2lo y2hi
  if dy == 0 then 0 else
  let wi := getAt wxList i
  let wi2 := getAt wxList i2
  let xlo := getAt exLoList i
  let xhi := getAt exHiList (i + 1)
  let x2lo := getAt exLoList i2
  let x2hi := getAt exHiList (i2 + 1)
  let dx := maxdistIv xlo xhi x2lo x2hi
  (100 * wi * wi2 * dy * dy) / (2 * dx * dx + dy * dy)

private def M12Int (i j l k : ℕ) : ℤ :=
  let xlo := getAt exLoList i
  let xhi := getAt exHiList (i + 1)
  let ylo := getAt eyList j
  let yhi := getAt eyList (j + 1)
  let ulo := getAt eyList k
  let uhi := getAt eyList (k + 1)
  let vlo := getAt exLoList l
  let vhi := getAt exHiList (l + 1)
  let dxMin := distIv xlo xhi ulo uhi
  let dxMax := maxdistIv xlo xhi ulo uhi
  let dyMin := distIv ylo yhi vlo vhi
  let dyMax := maxdistIv ylo yhi vlo vhi
  if dxMax ≥ dyMin ∧ dyMax ≥ dxMin then 0 else
  let dlo := if dxMax < dyMin then dxMax else dyMax
  let dhi := if dxMax < dyMin then dyMin else dxMin
  let wi := getAt wxList i
  let wl := getAt wxList l
  let diff := dhi - dlo
  let sum := dhi + dlo
  (100 * wi * wl * diff * diff) / (sum * sum)

private lemma distIv_nonneg (alo ahi blo bhi : ℤ) : 0 ≤ distIv alo ahi blo bhi := by
  unfold distIv; split_ifs <;> omega

private lemma wxList_pos (i : Fin 14) : 0 < getAt wxList i.1 := by
  fin_cases i <;> decide

private lemma tNumList_diff (i : Fin 14) :
    (getAtNat tNumList (i.1 + 1) : ℤ) - getAtNat tNumList i.1 = getAt wxList i.1 := by
  fin_cases i <;> decide

private lemma tNumList_mono (i : Fin 14) :
    getAtNat tNumList i.1 ≤ getAtNat tNumList (i.1 + 1) := by
  fin_cases i <;> decide

private lemma tNumList_range (i : Fin 15) : getAtNat tNumList i.1 ≤ 1000 := by
  fin_cases i <;> decide

private lemma eyList_mono (i : Fin 14) : getAt eyList i.1 ≤ getAt eyList (i.1 + 1) := by
  fin_cases i <;> decide

private lemma M1Int_nonneg (i j i2 j2 : Fin 14) : 0 ≤ M1Int i.1 j.1 i2.1 j2.1 := by
  unfold M1Int
  dsimp only
  split_ifs with h
  · exact le_rfl
  · refine Int.ediv_nonneg ?_ ?_
    · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (wxList_pos i).le)
        (wxList_pos i2).le) (distIv_nonneg _ _ _ _)) (distIv_nonneg _ _ _ _)
    · exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Int.natCast_nonneg _)) (Int.natCast_nonneg _))
        (mul_self_nonneg _)

private lemma M12Int_nonneg (i j l k : Fin 14) : 0 ≤ M12Int i.1 j.1 l.1 k.1 := by
  unfold M12Int
  dsimp only
  by_cases h :
      maxdistIv (getAt exLoList i.1) (getAt exHiList (i.1 + 1)) (getAt eyList k.1) (getAt eyList (k.1 + 1)) ≥
        distIv (getAt eyList j.1) (getAt eyList (j.1 + 1)) (getAt exLoList l.1) (getAt exHiList (l.1 + 1)) ∧
      maxdistIv (getAt eyList j.1) (getAt eyList (j.1 + 1)) (getAt exLoList l.1) (getAt exHiList (l.1 + 1)) ≥
        distIv (getAt exLoList i.1) (getAt exHiList (i.1 + 1)) (getAt eyList k.1) (getAt eyList (k.1 + 1))
  · rw [if_pos h]
  · rw [if_neg h]
    refine Int.ediv_nonneg ?_ (mul_self_nonneg _)
    rw [mul_assoc]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (wxList_pos i).le) (wxList_pos l).le)
      (mul_self_nonneg _)

private noncomputable def tEdge (i : Fin 15) : ℝ := (getAtNat tNumList i.1 : ℝ) / 1000
private noncomputable def exLo (i : Fin 15) : ℝ := (getAt exLoList i.1 : ℝ) / 10000
private noncomputable def exHi (i : Fin 15) : ℝ := (getAt exHiList i.1 : ℝ) / 10000
private noncomputable def eyEdge (i : Fin 15) : ℝ := (getAt eyList i.1 : ℝ) / 10000

private lemma tEdge_mono : Monotone tEdge := by
  have haux : ∀ b : ℕ, b ≤ 14 → ∀ a : ℕ, a ≤ b →
      getAtNat tNumList a ≤ getAtNat tNumList b := by
    intro b hb
    induction b with
    | zero => intro a ha; rw [Nat.eq_zero_of_le_zero ha]
    | succ k ih =>
      intro a ha
      rcases eq_or_lt_of_le ha with rfl | hlt
      · exact le_rfl
      · exact le_trans (ih (by omega) a (by omega)) (tNumList_mono ⟨k, by omega⟩)
  intro i j hij
  unfold tEdge
  exact div_le_div_of_nonneg_right (by exact_mod_cast haux j.1 (by omega) i.1 hij) (by norm_num)

private lemma eyEdge_mono : Monotone eyEdge := by
  have haux : ∀ b : ℕ, b ≤ 14 → ∀ a : ℕ, a ≤ b →
      getAt eyList a ≤ getAt eyList b := by
    intro b hb
    induction b with
    | zero => intro a ha; rw [Nat.eq_zero_of_le_zero ha]
    | succ k ih =>
      intro a ha
      rcases eq_or_lt_of_le ha with rfl | hlt
      · exact le_rfl
      · exact le_trans (ih (by omega) a (by omega)) (eyList_mono ⟨k, by omega⟩)
  intro i j hij
  unfold eyEdge
  exact div_le_div_of_nonneg_right (by exact_mod_cast haux j.1 (by omega) i.1 hij) (by norm_num)

private lemma tEdge_bounds (i : Fin 15) : 0 ≤ tEdge i ∧ tEdge i ≤ 1 := by
  unfold tEdge
  refine ⟨div_nonneg (Nat.cast_nonneg _) (by norm_num), ?_⟩
  rw [div_le_one (by norm_num)]
  exact_mod_cast tNumList_range i

private lemma alphaFn_tEdge_bounds (i : Fin 15) :
    exLo i ≤ alphaFn (tEdge i) ∧ alphaFn (tEdge i) ≤ exHi i := by
  have h1m : ∀ a b : ℝ, a + b = 1 → alphaFn a = 1 - alphaFn b := fun a b hab => by
    have : a = 1 - b := by linarith
    rw [this, alphaFn_symm]
  have hmid : alphaFn (1 / 2 : ℝ) = 1 / 2 := by
    unfold alphaFn
    rw [show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring, Real.cos_pi_div_two]
    norm_num
  fin_cases i
  · unfold tEdge exLo exHi alphaFn; norm_num [tNumList, exLoList, exHiList, getAt, getAtNat]
  · have h := alphaFn_bound_1
    unfold tEdge exLo exHi; norm_num [tNumList, exLoList, exHiList, getAt, getAtNat] at h ⊢; exact h
  · have h := alphaFn_bound_2
    unfold tEdge exLo exHi; norm_num [tNumList, exLoList, exHiList, getAt, getAtNat] at h ⊢; exact h
  · have h := alphaFn_bound_3
    unfold tEdge exLo exHi; norm_num [tNumList, exLoList, exHiList, getAt, getAtNat] at h ⊢; exact h
  · have h := alphaFn_bound_4
    unfold tEdge exLo exHi; norm_num [tNumList, exLoList, exHiList, getAt, getAtNat] at h ⊢; exact h
  · have h := alphaFn_bound_5
    unfold tEdge exLo exHi; norm_num [tNumList, exLoList, exHiList, getAt, getAtNat] at h ⊢; exact h
  · have h := alphaFn_bound_6
    unfold tEdge exLo exHi; norm_num [tNumList, exLoList, exHiList, getAt, getAtNat] at h ⊢; exact h
  · unfold tEdge exLo exHi
    norm_num [tNumList, exLoList, exHiList, getAt, getAtNat, hmid]
  · have h := alphaFn_bound_6
    unfold tEdge exLo exHi
    norm_num [tNumList, exLoList, exHiList, getAt, getAtNat] at h ⊢
    rw [h1m (531 / 1000 : ℝ) (469 / 1000 : ℝ) (by norm_num)]
    constructor <;> linarith
  · have h := alphaFn_bound_5
    unfold tEdge exLo exHi
    norm_num [tNumList, exLoList, exHiList, getAt, getAtNat] at h ⊢
    rw [h1m (571 / 1000 : ℝ) (429 / 1000 : ℝ) (by norm_num)]
    constructor <;> linarith
  · have h := alphaFn_bound_4
    unfold tEdge exLo exHi
    norm_num [tNumList, exLoList, exHiList, getAt, getAtNat] at h ⊢
    rw [h1m (309 / 500 : ℝ) (191 / 500 : ℝ) (by norm_num)]
    constructor <;> linarith
  · have h := alphaFn_bound_3
    unfold tEdge exLo exHi
    norm_num [tNumList, exLoList, exHiList, getAt, getAtNat] at h ⊢
    rw [h1m (671 / 1000 : ℝ) (329 / 1000 : ℝ) (by norm_num)]
    constructor <;> linarith
  · have h := alphaFn_bound_2
    unfold tEdge exLo exHi
    norm_num [tNumList, exLoList, exHiList, getAt, getAtNat] at h ⊢
    rw [h1m (733 / 1000 : ℝ) (267 / 1000 : ℝ) (by norm_num)]
    constructor <;> linarith
  · have h := alphaFn_bound_1
    unfold tEdge exLo exHi
    norm_num [tNumList, exLoList, exHiList, getAt, getAtNat] at h ⊢
    rw [h1m (203 / 250 : ℝ) (47 / 250 : ℝ) (by norm_num)]
    constructor <;> linarith
  · unfold tEdge exLo exHi alphaFn; norm_num [tNumList, exLoList, exHiList, getAt, getAtNat]

private def tBucket (i : Fin 14) : Set ℝ :=
  Ioo (0 : ℝ) 1 ∩ Ico (tEdge i.castSucc) (tEdge i.succ)

private lemma measurableSet_tBucket (i : Fin 14) : MeasurableSet (tBucket i) :=
  measurableSet_Ioo.inter measurableSet_Ico

private lemma tBucket_disjoint : Pairwise fun i j : Fin 14 => Disjoint (tBucket i) (tBucket j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro t hti htj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hle : i.succ ≤ j.castSucc := Fin.succ_le_castSucc_iff.mpr hlt
    linarith [hti.2.2, htj.2.1, tEdge_mono hle]
  · have hle : j.succ ≤ i.castSucc := Fin.succ_le_castSucc_iff.mpr hgt
    linarith [htj.2.2, hti.2.1, tEdge_mono hle]

private lemma lam0_tBucket (i : Fin 14) :
    lam0 (tBucket i) = ENNReal.ofReal ((getAt wxList i.1 : ℝ) / 1000) := by
  have hi1 : Ioo (tEdge i.castSucc) (tEdge i.succ) ⊆ tBucket i := fun t ht =>
    ⟨⟨lt_of_le_of_lt (tEdge_bounds i.castSucc).1 ht.1, lt_of_lt_of_le ht.2 (tEdge_bounds i.succ).2⟩,
     ht.1.le, ht.2⟩
  have hi2 : tBucket i ⊆ Icc (tEdge i.castSucc) (tEdge i.succ) := fun t ht =>
    ⟨ht.2.1, ht.2.2.le⟩
  have hdiff : tEdge i.succ - tEdge i.castSucc = (getAt wxList i.1 : ℝ) / 1000 := by
    unfold tEdge
    simp only [Fin.val_succ, Fin.val_castSucc]
    have hd := tNumList_diff i
    have hdr : ((getAtNat tNumList (i.1 + 1) : ℤ) - getAtNat tNumList i.1 : ℝ) = (getAt wxList i.1 : ℝ) := by
      exact_mod_cast hd
    push_cast at hdr
    linarith
  have hlam : lam0 (tBucket i) = volume (tBucket i) := by
    rw [lam0, Measure.restrict_apply (measurableSet_tBucket i)]
    have : tBucket i ∩ Ioo (0 : ℝ) 1 = tBucket i := Set.inter_eq_left.mpr fun _ h => h.1
    rw [this]
  rw [hlam]
  refine le_antisymm ?_ ?_
  · calc volume (tBucket i)
        ≤ volume (Icc (tEdge i.castSucc) (tEdge i.succ)) := measure_mono hi2
      _ = ENNReal.ofReal (tEdge i.succ - tEdge i.castSucc) := Real.volume_Icc
      _ = ENNReal.ofReal ((getAt wxList i.1 : ℝ) / 1000) := by rw [hdiff]
  · calc ENNReal.ofReal ((getAt wxList i.1 : ℝ) / 1000)
        = ENNReal.ofReal (tEdge i.succ - tEdge i.castSucc) := by rw [hdiff]
      _ = volume (Ioo (tEdge i.castSucc) (tEdge i.succ)) := Real.volume_Ioo.symm
      _ ≤ volume (tBucket i) := measure_mono hi1

private lemma alphaFn_mem_bucket (i : Fin 14) {t : ℝ} (ht : t ∈ tBucket i) :
    exLo i.castSucc ≤ alphaFn t ∧ alphaFn t ≤ exHi i.succ := by
  have hmono := alphaFn_strictMonoOn.monotoneOn
  have ht0 := tEdge_bounds i.castSucc
  have ht1 := tEdge_bounds i.succ
  have hb0 := alphaFn_tEdge_bounds i.castSucc
  have hb1 := alphaFn_tEdge_bounds i.succ
  have hle1 : alphaFn (tEdge i.castSucc) ≤ alphaFn t :=
    hmono ht0 ⟨ht.1.1.le, ht.1.2.le⟩ ht.2.1
  have hle2 : alphaFn t ≤ alphaFn (tEdge i.succ) :=
    hmono ⟨ht.1.1.le, ht.1.2.le⟩ ht1 ht.2.2.le
  exact ⟨le_trans hb0.1 hle1, le_trans hle2 hb1.2⟩

private def yBucket (j : Fin 14) : Set ℝ :=
  if j.1 < 13 then Ico (eyEdge j.castSucc) (eyEdge j.succ)
  else Icc (eyEdge j.castSucc) (eyEdge j.succ)

private lemma measurableSet_yBucket (j : Fin 14) : MeasurableSet (yBucket j) := by
  unfold yBucket; split_ifs <;> [exact measurableSet_Ico; exact measurableSet_Icc]

private lemma yBucket_bounds {j : Fin 14} {v : ℝ} (hv : v ∈ yBucket j) :
    eyEdge j.castSucc ≤ v ∧ v ≤ eyEdge j.succ := by
  unfold yBucket at hv
  split_ifs at hv
  · exact ⟨hv.1, hv.2.le⟩
  · exact hv

private lemma yBucket_disjoint : Pairwise fun j₁ j₂ : Fin 14 => Disjoint (yBucket j₁) (yBucket j₂) := by
  intro j₁ j₂ hij
  rw [Set.disjoint_left]
  intro v hv₁ hv₂
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hj1 : j₁.1 < 13 := by omega
    unfold yBucket at hv₁
    rw [if_pos hj1] at hv₁
    have hv₂b := yBucket_bounds hv₂
    have hle : j₁.succ ≤ j₂.castSucc := Fin.succ_le_castSucc_iff.mpr hlt
    linarith [hv₁.2, hv₂b.1, eyEdge_mono hle]
  · have hj2 : j₂.1 < 13 := by omega
    unfold yBucket at hv₂
    rw [if_pos hj2] at hv₂
    have hv₁b := yBucket_bounds hv₁
    have hle : j₂.succ ≤ j₁.castSucc := Fin.succ_le_castSucc_iff.mpr hgt
    linarith [hv₂.2, hv₁b.1, eyEdge_mono hle]

private lemma yBucket_covering {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) : ∃ j : Fin 14, v ∈ yBucket j := by
  have he0 : eyEdge 0 = 0 := by unfold eyEdge; norm_num [eyList, getAt]
  have he14 : eyEdge 14 = 1 := by unfold eyEdge; norm_num [eyList, getAt]
  rcases eq_or_lt_of_le hv.2 with rfl | hvlt
  · refine ⟨⟨13, by omega⟩, ?_⟩
    unfold yBucket
    rw [if_neg (by decide)]
    exact ⟨by simpa [he14] using eyEdge_mono (show (⟨13, by omega⟩ : Fin 15) ≤ 14 by decide),
           by simp [he14]⟩
  · have aux : ∀ k : ℕ, ∀ hk : k ≤ 14, v < eyEdge ⟨k, Nat.lt_succ_of_le hk⟩ →
        ∃ j : Fin 14, j.1 < k ∧ v ∈ yBucket j := by
      intro k hk hlt
      induction k with
      | zero =>
        change v < eyEdge 0 at hlt
        linarith [hv.1, he0]
      | succ m ih =>
        by_cases hm : v < eyEdge ⟨m, Nat.lt_succ_of_le (by omega)⟩
        · obtain ⟨j, hj1, hj2⟩ := ih (by omega) hm
          exact ⟨j, Nat.lt_succ_of_lt hj1, hj2⟩
        · push Not at hm
          refine ⟨⟨m, by omega⟩, Nat.lt_succ_self m, ?_⟩
          unfold yBucket
          split_ifs
          · exact ⟨hm, hlt⟩
          · exact ⟨hm, hlt.le⟩
    obtain ⟨j, _, hj⟩ := aux 14 le_rfl (by simpa [he14] using hvlt)
    exact ⟨j, hj⟩

private abbrev Idx := Bool × Fin 14 × Fin 14

private def cell (y u : ℝ → ℝ) : Idx → Set ℝ
  | (false, i, j) => tBucket i ∩ y ⁻¹' yBucket j
  | (true, i, j) => tBucket i ∩ u ⁻¹' yBucket j

private lemma measurableSet_cell {y u : ℝ → ℝ} (hym : Measurable y) (hum : Measurable u) (a : Idx) :
    MeasurableSet (cell y u a) := by
  rcases a with ⟨p, i, j⟩
  cases p
  · exact (measurableSet_tBucket i).inter (hym (measurableSet_yBucket j))
  · exact (measurableSet_tBucket i).inter (hum (measurableSet_yBucket j))

private lemma cell_disjoint_side (y u : ℝ → ℝ) (p : Bool) :
    Pairwise fun a b : Fin 14 × Fin 14 => Disjoint (cell y u (p, a)) (cell y u (p, b)) := by
  intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hne
  by_cases hi : i₁ = i₂
  · subst hi
    have hj : j₁ ≠ j₂ := fun h => hne (by subst h; rfl)
    cases p <;> exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
      ((yBucket_disjoint hj).preimage _)
  · cases p <;> exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left (tBucket_disjoint hi)

private noncomputable def zVec (y u : ℝ → ℝ) (a : Idx) : ℝ :=
  (lam0 (cell y u a)).toReal / ((getAt wxList a.2.1.1 : ℝ) / 1000)

private lemma zVec_nonneg (y u : ℝ → ℝ) (a : Idx) : 0 ≤ zVec y u a := by
  unfold zVec
  have hw : (0 : ℝ) < (getAt wxList a.2.1.1 : ℝ) / 1000 := by
    have : (0 : ℝ) < getAt wxList a.2.1.1 := by exact_mod_cast wxList_pos a.2.1
    linarith
  exact div_nonneg ENNReal.toReal_nonneg hw.le

private lemma zVec_row_sum {y u : ℝ → ℝ} (hy_mem : ∀ t, y t ∈ Icc (0 : ℝ) 1)
    (hu_mem : ∀ t, u t ∈ Icc (0 : ℝ) 1) (hym : Measurable y) (hum : Measurable u)
    (p : Bool) (i : Fin 14) :
    ∑ j : Fin 14, zVec y u (p, i, j) = 1 := by
  have helper : ∀ (g : ℝ → ℝ), Measurable g → (∀ t, g t ∈ Icc (0 : ℝ) 1) →
      ∑ j : Fin 14, (lam0 (tBucket i ∩ g ⁻¹' yBucket j)).toReal / ((getAt wxList i.1 : ℝ) / 1000) = 1 := by
    intro g hgm hg
    have hunion : (⋃ j ∈ (Finset.univ : Finset (Fin 14)), (tBucket i ∩ g ⁻¹' yBucket j)) = tBucket i := by
      ext t
      simp only [Set.mem_iUnion, Finset.mem_univ, Set.mem_inter_iff, Set.mem_preimage, exists_prop, true_and]
      constructor
      · rintro ⟨_, ht, _⟩; exact ht
      · intro ht
        obtain ⟨j, hj⟩ := yBucket_covering (hg t)
        exact ⟨j, ht, hj⟩
    have hsum_meas : lam0 (tBucket i) = ∑ j : Fin 14, lam0 (tBucket i ∩ g ⁻¹' yBucket j) := by
      conv_lhs => rw [← hunion]
      exact measure_biUnion_finset (fun j₁ _ j₂ _ hne =>
        Disjoint.mono Set.inter_subset_right Set.inter_subset_right ((yBucket_disjoint hne).preimage g))
        (fun j _ => (measurableSet_tBucket i).inter (hgm (measurableSet_yBucket j)))
    have hsum_real : (lam0 (tBucket i)).toReal = ∑ j : Fin 14, (lam0 (tBucket i ∩ g ⁻¹' yBucket j)).toReal := by
      rw [hsum_meas]
      exact ENNReal.toReal_sum fun j _ => ne_top_of_lt (measure_lt_top lam0 _)
    rw [← Finset.sum_div, ← hsum_real, lam0_tBucket, ENNReal.toReal_ofReal]
    · have hwpos : (0 : ℝ) < (getAt wxList i.1 : ℝ) / 1000 := by
        have : (0 : ℝ) < getAt wxList i.1 := by exact_mod_cast wxList_pos i
        linarith
      exact div_self hwpos.ne'
    · have : (0 : ℝ) < getAt wxList i.1 := by exact_mod_cast wxList_pos i
      linarith
  cases p
  · exact helper y hym hy_mem
  · exact helper u hum hu_mem

private lemma integral_prod_partition_ge {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {A : ι₁ → Set ℝ} {B : ι₂ → Set ℝ}
    (hAm : ∀ a, MeasurableSet (A a)) (hBm : ∀ b, MeasurableSet (B b))
    (hAd : Pairwise fun a₁ a₂ => Disjoint (A a₁) (A a₂))
    (hBd : Pairwise fun b₁ b₂ => Disjoint (B b₁) (B b₂))
    {F : ℝ × ℝ → ℝ} (hFi : Integrable F (lam0.prod lam0)) (hF0 : ∀ pr, 0 ≤ F pr)
    {S : Set (ℝ × ℝ)} (hS : ∀ᵐ pr ∂(lam0.prod lam0), pr ∈ S)
    {c : ι₁ → ι₂ → ℝ} (hc0 : ∀ a b, 0 ≤ c a b)
    (hcb : ∀ a b, ∀ x ∈ A a, ∀ y ∈ B b, (x, y) ∈ S → c a b ≤ F (x, y)) :
    ∑ a : ι₁, ∑ b : ι₂, (lam0 (A a)).toReal * (lam0 (B b)).toReal * c a b ≤
      ∫ pr : ℝ × ℝ, F pr ∂(lam0.prod lam0) := by
  let G : ℝ × ℝ → ℝ := fun pr =>
    ∑ a : ι₁, ∑ b : ι₂, (A a ×ˢ B b).indicator (fun _ => c a b) pr
  have hterm_int : ∀ a : ι₁, ∀ b : ι₂,
      Integrable (fun pr : ℝ × ℝ => (A a ×ˢ B b).indicator (fun _ => c a b) pr) (lam0.prod lam0) := by
    intro a b
    rw [integrable_indicator_iff ((hAm a).prod (hBm b))]
    exact (integrableOn_const (hs := measure_ne_top (lam0.prod lam0) _))
  have hGi : Integrable G (lam0.prod lam0) :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hterm_int a b
  have hG_eq : ∫ pr : ℝ × ℝ, G pr ∂(lam0.prod lam0) =
      ∑ a : ι₁, ∑ b : ι₂, (lam0 (A a)).toReal * (lam0 (B b)).toReal * c a b := by
    dsimp [G]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hterm_int a b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => hterm_int a b]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_indicator ((hAm a).prod (hBm b)), setIntegral_const, smul_eq_mul,
      Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  have hle : ∀ᵐ pr ∂(lam0.prod lam0), G pr ≤ F pr := by
    filter_upwards [hS] with pr hprS
    dsimp [G]
    by_cases hex : ∃ a : ι₁, ∃ b : ι₂, pr ∈ A a ×ˢ B b
    · obtain ⟨a₀, b₀, hmem⟩ := hex
      have hsum_a : ∑ a : ι₁, ∑ b : ι₂, (A a ×ˢ B b).indicator (fun _ => c a b) pr = c a₀ b₀ := by
        rw [Finset.sum_eq_single a₀]
        · rw [Finset.sum_eq_single b₀]
          · exact Set.indicator_of_mem hmem _
          · intro b _ hne
            apply Set.indicator_of_notMem
            intro hmem'
            exact (Set.disjoint_left.mp (hBd hne)) hmem'.2 hmem.2
          · intro hn; exact absurd (Finset.mem_univ b₀) hn
        · intro a _ hne
          refine Finset.sum_eq_zero fun b _ => ?_
          apply Set.indicator_of_notMem
          intro hmem'
          exact (Set.disjoint_left.mp (hAd hne)) hmem'.1 hmem.1
        · intro hn; exact absurd (Finset.mem_univ a₀) hn
      rw [hsum_a]
      exact hcb a₀ b₀ pr.1 hmem.1 pr.2 hmem.2 hprS
    · push Not at hex
      have hzero : ∑ a : ι₁, ∑ b : ι₂, (A a ×ˢ B b).indicator (fun _ => c a b) pr = 0 :=
        Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
          Set.indicator_of_notMem (hex a b) _
      rw [hzero]
      exact hF0 pr
  rw [← hG_eq]
  exact integral_mono_ae hGi hFi hle

private lemma distIv_le_abs {alo ahi blo bhi : ℤ} {a b : ℝ}
    (ha1 : (alo : ℝ) / 10000 ≤ a) (ha2 : a ≤ (ahi : ℝ) / 10000)
    (hb1 : (blo : ℝ) / 10000 ≤ b) (hb2 : b ≤ (bhi : ℝ) / 10000) :
    (distIv alo ahi blo bhi : ℝ) / 10000 ≤ |a - b| := by
  unfold distIv
  split_ifs with h1 h2
  · simp only [Int.cast_zero, zero_div]; exact abs_nonneg _
  · have h3 : (ahi : ℝ) / 10000 < (blo : ℝ) / 10000 := by
      have : (ahi : ℝ) < (blo : ℝ) := by exact_mod_cast h2
      linarith
    rw [abs_of_nonpos (by linarith)]
    push_cast; linarith
  · have hno : bhi < alo := by omega
    have h3 : (bhi : ℝ) / 10000 < (alo : ℝ) / 10000 := by
      have : (bhi : ℝ) < (alo : ℝ) := by exact_mod_cast hno
      linarith
    rw [abs_of_nonneg (by linarith)]
    push_cast; linarith

private lemma abs_le_maxdistIv {alo ahi blo bhi : ℤ} {a b : ℝ}
    (ha1 : (alo : ℝ) / 10000 ≤ a) (ha2 : a ≤ (ahi : ℝ) / 10000)
    (hb1 : (blo : ℝ) / 10000 ≤ b) (hb2 : b ≤ (bhi : ℝ) / 10000) :
    |a - b| ≤ (maxdistIv alo ahi blo bhi : ℝ) / 10000 := by
  unfold maxdistIv
  let n : ℕ := if Int.natAbs (alo - bhi) ≥ Int.natAbs (ahi - blo)
    then Int.natAbs (alo - bhi) else Int.natAbs (ahi - blo)
  have h1z : |(alo : ℤ) - bhi| ≤ (n : ℤ) := by
    rw [Int.abs_eq_natAbs]; dsimp [n]; split_ifs <;> omega
  have h2z : |(ahi : ℤ) - blo| ≤ (n : ℤ) := by
    rw [Int.abs_eq_natAbs]; dsimp [n]; split_ifs <;> omega
  have h1r : |(alo : ℝ) - bhi| ≤ (n : ℝ) := by exact_mod_cast h1z
  have h2r : |(ahi : ℝ) - blo| ≤ (n : ℝ) := by exact_mod_cast h2z
  rw [abs_le] at h1r h2r ⊢
  change -((n : ℝ) / 10000) ≤ a - b ∧ a - b ≤ (n : ℝ) / 10000
  constructor <;> linarith

private lemma e1Rat_ge_M1Int {i j i2 j2 : Fin 14} {x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : exLo i.castSucc ≤ x₁ ∧ x₁ ≤ exHi i.succ)
    (hx₂ : exLo i2.castSucc ≤ x₂ ∧ x₂ ≤ exHi i2.succ)
    (hy₁ : eyEdge j.castSucc ≤ y₁ ∧ y₁ ≤ eyEdge j.succ)
    (hy₂ : eyEdge j2.castSucc ≤ y₂ ∧ y₂ ≤ eyEdge j2.succ)
    (hxne : x₁ ≠ x₂) :
    (M1Int i.1 j.1 i2.1 j2.1 : ℝ) / (100 * (getAt wxList i.1 : ℝ) * (getAt wxList i2.1 : ℝ)) ≤
      e1Rat x₁ y₁ x₂ y₂ := by
  unfold M1Int
  dsimp only
  set dy := distIv (getAt eyList j.1) (getAt eyList (j.1 + 1)) (getAt eyList j2.1) (getAt eyList (j2.1 + 1))
  by_cases hdy0 : dy = 0
  · simp [hdy0]; exact (e1Rat_bounds x₁ y₁ x₂ y₂).1
  · have hdy_pos : 0 < dy := lt_of_le_of_ne (distIv_nonneg _ _ _ _) (Ne.symm hdy0)
    have hif : (dy == 0) = false := by simp [hdy0]
    rw [if_neg (by simp [hdy0])]
    set wi := getAt wxList i.1
    set wi2 := getAt wxList i2.1
    set dx := maxdistIv (getAt exLoList i.1) (getAt exHiList (i.1 + 1)) (getAt exLoList i2.1) (getAt exHiList (i2.1 + 1))
    have hdx_nn : 0 ≤ dx := by dsimp [dx, maxdistIv]; exact Int.natCast_nonneg _
    have hwi_pos : 0 < (wi : ℝ) := by exact_mod_cast wxList_pos i
    have hwi2_pos : 0 < (wi2 : ℝ) := by exact_mod_cast wxList_pos i2
    have hdy_r : (dy : ℝ) / 10000 ≤ |y₁ - y₂| := distIv_le_abs hy₁.1 hy₁.2 hy₂.1 hy₂.2
    have hdx_r : |x₁ - x₂| ≤ (dx : ℝ) / 10000 := abs_le_maxdistIv hx₁.1 hx₁.2 hx₂.1 hx₂.2
    have hdy_pos_r : (0 : ℝ) < (dy : ℝ) / 10000 := by
      have : (0 : ℝ) < dy := by exact_mod_cast hdy_pos
      linarith
    have hdx_pos_r : 0 < |x₁ - x₂| := abs_pos.mpr (sub_ne_zero.mpr hxne)
    have he1 : e1Rat x₁ y₁ x₂ y₂ = |y₁ - y₂| ^ 2 / (2 * |x₁ - x₂| ^ 2 + |y₁ - y₂| ^ 2) := by
      unfold e1Rat; dsimp only
      rw [if_neg (sub_ne_zero.mpr hxne), sq_abs, sq_abs]
      have hne0 : (x₁ - x₂) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hxne)
      field_simp [hne0]
    have hmono : ((dy : ℝ) / 10000) ^ 2 / (2 * ((dx : ℝ) / 10000) ^ 2 + ((dy : ℝ) / 10000) ^ 2) ≤
        e1Rat x₁ y₁ x₂ y₂ := by
      rw [he1, div_le_div_iff₀ (by positivity) (by positivity)]
      have hsq : ((dy : ℝ) / 10000) ^ 2 * |x₁ - x₂| ^ 2 ≤ |y₁ - y₂| ^ 2 * ((dx : ℝ) / 10000) ^ 2 :=
        mul_le_mul (pow_le_pow_left₀ hdy_pos_r.le hdy_r 2) (pow_le_pow_left₀ hdx_pos_r.le hdx_r 2)
          (sq_nonneg _) (sq_nonneg _)
      linarith
    have hden_pos : 0 < 2 * dx * dx + dy * dy := by nlinarith
    have hed := Int.ediv_mul_le (100 * wi * wi2 * dy * dy) hden_pos.ne'
    have hed_r : (((100 * wi * wi2 * dy * dy) / (2 * dx * dx + dy * dy) : ℤ) : ℝ) *
        (2 * (dx : ℝ) ^ 2 + (dy : ℝ) ^ 2) ≤
        100 * (wi : ℝ) * (wi2 : ℝ) * (dy : ℝ) ^ 2 := by
      have h1 : (((100 * wi * wi2 * dy * dy) / (2 * dx * dx + dy * dy) * (2 * dx * dx + dy * dy) : ℤ) : ℝ) ≤
          ((100 * wi * wi2 * dy * dy : ℤ) : ℝ) := by exact_mod_cast hed
      push_cast at h1
      ring_nf at h1 ⊢
      exact h1
    have hrat_eq : ((dy : ℝ) / 10000) ^ 2 / (2 * ((dx : ℝ) / 10000) ^ 2 + ((dy : ℝ) / 10000) ^ 2) =
        (dy : ℝ) ^ 2 / (2 * (dx : ℝ) ^ 2 + (dy : ℝ) ^ 2) := by
      have hden_r : 2 * (dx : ℝ) ^ 2 + (dy : ℝ) ^ 2 ≠ 0 := by positivity
      field_simp
    have hcert : (((100 * wi * wi2 * dy * dy) / (2 * dx * dx + dy * dy) : ℤ) : ℝ) /
        (100 * (wi : ℝ) * (wi2 : ℝ)) ≤
        (dy : ℝ) ^ 2 / (2 * (dx : ℝ) ^ 2 + (dy : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    rw [hrat_eq] at hmono
    exact le_trans hcert hmono

private lemma e12Rat_ge_M12Int {i j l k : Fin 14} {x y u v : ℝ}
    (hx : exLo i.castSucc ≤ x ∧ x ≤ exHi i.succ)
    (hy : eyEdge j.castSucc ≤ y ∧ y ≤ eyEdge j.succ)
    (hu : eyEdge k.castSucc ≤ u ∧ u ≤ eyEdge k.succ)
    (hv : exLo l.castSucc ≤ v ∧ v ≤ exHi l.succ)
    (hxune : x ≠ u) (hyvne : y ≠ v) :
    (M12Int i.1 j.1 l.1 k.1 : ℝ) / (100 * (getAt wxList i.1 : ℝ) * (getAt wxList l.1 : ℝ)) ≤
      e12Rat x y u v := by
  unfold M12Int
  dsimp only
  set wi := getAt wxList i.1
  set wl := getAt wxList l.1
  set dxMin := distIv (getAt exLoList i.1) (getAt exHiList (i.1 + 1)) (getAt eyList k.1) (getAt eyList (k.1 + 1))
  set dxMax := maxdistIv (getAt exLoList i.1) (getAt exHiList (i.1 + 1)) (getAt eyList k.1) (getAt eyList (k.1 + 1))
  set dyMin := distIv (getAt eyList j.1) (getAt eyList (j.1 + 1)) (getAt exLoList l.1) (getAt exHiList (l.1 + 1))
  set dyMax := maxdistIv (getAt eyList j.1) (getAt eyList (j.1 + 1)) (getAt exLoList l.1) (getAt exHiList (l.1 + 1))
  by_cases hzero : dxMax ≥ dyMin ∧ dyMax ≥ dxMin
  · rw [if_pos hzero]; simp; exact (e12Rat_bounds x y u v).1
  · rw [if_neg hzero]
    have hwi_pos : 0 < (wi : ℝ) := by exact_mod_cast wxList_pos i
    have hwl_pos : 0 < (wl : ℝ) := by exact_mod_cast wxList_pos l
    have hdx_pos : 0 < |x - u| := abs_pos.mpr (sub_ne_zero.mpr hxune)
    have hdy_pos : 0 < |y - v| := abs_pos.mpr (sub_ne_zero.mpr hyvne)
    have hdx_lo : (dxMin : ℝ) / 10000 ≤ |x - u| := distIv_le_abs hx.1 hx.2 hu.1 hu.2
    have hdx_hi : |x - u| ≤ (dxMax : ℝ) / 10000 := abs_le_maxdistIv hx.1 hx.2 hu.1 hu.2
    have hdy_lo : (dyMin : ℝ) / 10000 ≤ |y - v| := distIv_le_abs hy.1 hy.2 hv.1 hv.2
    have hdy_hi : |y - v| ≤ (dyMax : ℝ) / 10000 := abs_le_maxdistIv hy.1 hy.2 hv.1 hv.2
    have he12 : e12Rat x y u v = ((|x - u| - |y - v|) / (|x - u| + |y - v|)) ^ 2 := by
      unfold e12Rat; dsimp only
      rw [if_neg (not_or.mpr ⟨hdx_pos.ne', hdy_pos.ne'⟩)]
    set dlo := if dxMax < dyMin then dxMax else dyMax
    set dhi := if dxMax < dyMin then dyMin else dxMin
    have hd_lt : dlo < dhi := by
      dsimp [dlo, dhi]
      by_cases h : dxMax < dyMin
      · simp [h]
      · simp [h]; omega
    have hsum_pos : 0 < dhi + dlo := by
      have : 0 ≤ dlo := by
        dsimp [dlo]; split_ifs <;> [exact Int.natCast_nonneg _; exact Int.natCast_nonneg _]
      omega
    have hed := Int.ediv_mul_le (100 * wi * wl * (dhi - dlo) * (dhi - dlo)) (mul_pos hsum_pos hsum_pos).ne'
    have hcert : (((100 * wi * wl * (dhi - dlo) * (dhi - dlo)) / ((dhi + dlo) * (dhi + dlo)) : ℤ) : ℝ) /
        (100 * (wi : ℝ) * (wl : ℝ)) ≤
        ((dhi - dlo : ℝ) / (dhi + dlo)) ^ 2 := by
      have h1 : (((100 * wi * wl * (dhi - dlo) * (dhi - dlo)) / ((dhi + dlo) * (dhi + dlo)) *
          ((dhi + dlo) * (dhi + dlo)) : ℤ) : ℝ) ≤
          ((100 * wi * wl * (dhi - dlo) * (dhi - dlo) : ℤ) : ℝ) := by exact_mod_cast hed
      push_cast at h1
      have hsum_r : (0 : ℝ) < (dhi : ℝ) + (dlo : ℝ) := by exact_mod_cast hsum_pos
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hmono : ((dhi - dlo : ℝ) / (dhi + dlo)) ^ 2 ≤ e12Rat x y u v := by
      rw [he12]
      have hratio_ge : ∀ a b : ℝ, 0 < a → a ≤ (dlo : ℝ) / 10000 → (dhi : ℝ) / 10000 ≤ b →
          ((dhi - dlo : ℝ) / (dhi + dlo)) ^ 2 ≤ ((b - a) / (b + a)) ^ 2 := by
        intro a b ha0 ha1 hb1
        have hd_lt_r : (dlo : ℝ) / 10000 < (dhi : ℝ) / 10000 := by
          have : (dlo : ℝ) < dhi := by exact_mod_cast hd_lt
          linarith
        have hsum_r : (0 : ℝ) < (dhi : ℝ) + (dlo : ℝ) := by exact_mod_cast hsum_pos
        have hr1 : ((dhi - dlo : ℝ) / (dhi + dlo)) =
            ((dhi : ℝ) / 10000 - (dlo : ℝ) / 10000) / ((dhi : ℝ) / 10000 + (dlo : ℝ) / 10000) := by
          field_simp [hsum_r.ne']
        rw [hr1]
        apply pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith))
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith
      by_cases hlt : dxMax < dyMin
      · have hd1 : dlo = dxMax := if_pos hlt
        have hd2 : dhi = dyMin := if_pos hlt
        rw [hd1, hd2]
        have h1 := hratio_ge |x - u| |y - v| hdx_pos (hd1 ▸ hdx_hi) (hd2 ▸ hdy_lo)
        calc (((dyMin : ℝ) - dxMax) / (dyMin + dxMax)) ^ 2
            ≤ ((|y - v| - |x - u|) / (|y - v| + |x - u|)) ^ 2 := by simpa [hd1, hd2] using h1
          _ = ((|x - u| - |y - v|) / (|x - u| + |y - v|)) ^ 2 := by
            have : (|y - v| - |x - u|) / (|y - v| + |x - u|) = -((|x - u| - |y - v|) / (|x - u| + |y - v|)) := by
              ring
            rw [this, neg_sq]
      · have hgt : dyMax < dxMin := by omega
        have hd1 : dlo = dyMax := if_neg hlt
        have hd2 : dhi = dxMin := if_neg hlt
        rw [hd1, hd2]
        simpa [hd1, hd2] using hratio_ge |y - v| |x - u| hdy_pos (hd1 ▸ hdy_hi) (hd2 ▸ hdx_lo)
    exact le_trans hcert hmono

private def M_int : Idx → Idx → ℤ
  | (false, i, j), (false, i2, j2) => M1Int i.1 j.1 i2.1 j2.1
  | (true, i, j), (true, i2, j2) => M1Int i.1 j.1 i2.1 j2.1
  | (false, i, j), (true, l, k) => M12Int i.1 j.1 l.1 k.1
  | (true, l, k), (false, i, j) => M12Int i.1 j.1 l.1 k.1

private lemma M_int_nonneg (a b : Idx) : 0 ≤ M_int a b := by
  rcases a with ⟨p, i, j⟩
  rcases b with ⟨q, l, k⟩
  cases p <;> cases q <;> [exact M1Int_nonneg i j l k; exact M12Int_nonneg i j l k;
    exact M12Int_nonneg l k i j; exact M1Int_nonneg i j l k]

private lemma energyRat_ge_M_int {y u : ℝ → ℝ}
    (hym : Measurable y) (hum : Measurable u)
    (hy_mem : ∀ t, y t ∈ Icc (0 : ℝ) 1) (hu_mem : ∀ t, u t ∈ Icc (0 : ℝ) 1) :
    ∑ a : Idx, ∑ b : Idx, zVec y u a * zVec y u b * (M_int a b : ℝ) ≤
      400000000 * energyRat y u := by
  have hcont_alpha : Continuous alphaFn := by unfold alphaFn; fun_prop
  have hm_e1_y : Integrable (fun pr : ℝ × ℝ => e1Rat (alphaFn pr.1) (y pr.1) (alphaFn pr.2) (y pr.2)) (lam0.prod lam0) := by
    refine (integrable_const (1 : ℝ)).mono ?_ (ae_of_all _ fun pr => ?_)
    · unfold e1Rat
      have hm1 : Measurable (fun pr : ℝ × ℝ => (alphaFn pr.1 - alphaFn pr.2)) :=
        (hcont_alpha.measurable.comp measurable_fst).sub (hcont_alpha.measurable.comp measurable_snd)
      have hm2 : Measurable (fun pr : ℝ × ℝ => (y pr.1 - y pr.2)) :=
        (hym.comp measurable_fst).sub (hym.comp measurable_snd)
      exact (Measurable.ite (hm1 (measurableSet_singleton 0)) measurable_const
        (((hm2.pow_const 2).div (hm1.pow_const 2)).div (measurable_const.add ((hm2.pow_const 2).div (hm1.pow_const 2))))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (e1Rat_bounds _ _ _ _).1, norm_one]
      exact (e1Rat_bounds _ _ _ _).2
  have hm_e1_u : Integrable (fun pr : ℝ × ℝ => e1Rat (alphaFn pr.1) (u pr.1) (alphaFn pr.2) (u pr.2)) (lam0.prod lam0) := by
    refine (integrable_const (1 : ℝ)).mono ?_ (ae_of_all _ fun pr => ?_)
    · unfold e1Rat
      have hm1 : Measurable (fun pr : ℝ × ℝ => (alphaFn pr.1 - alphaFn pr.2)) :=
        (hcont_alpha.measurable.comp measurable_fst).sub (hcont_alpha.measurable.comp measurable_snd)
      have hm2 : Measurable (fun pr : ℝ × ℝ => (u pr.1 - u pr.2)) :=
        (hum.comp measurable_fst).sub (hum.comp measurable_snd)
      exact (Measurable.ite (hm1 (measurableSet_singleton 0)) measurable_const
        (((hm2.pow_const 2).div (hm1.pow_const 2)).div (measurable_const.add ((hm2.pow_const 2).div (hm1.pow_const 2))))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (e1Rat_bounds _ _ _ _).1, norm_one]
      exact (e1Rat_bounds _ _ _ _).2
  have hm_e12 : Integrable (fun pr : ℝ × ℝ => e12Rat (alphaFn pr.1) (y pr.1) (u pr.2) (alphaFn pr.2)) (lam0.prod lam0) := by
    refine (integrable_const (1 : ℝ)).mono ?_ (ae_of_all _ fun pr => ?_)
    · unfold e12Rat
      have hm1 : Measurable (fun pr : ℝ × ℝ => |alphaFn pr.1 - u pr.2|) :=
        continuous_abs.measurable.comp ((hcont_alpha.measurable.comp measurable_fst).sub (hum.comp measurable_snd))
      have hm2 : Measurable (fun pr : ℝ × ℝ => |y pr.1 - alphaFn pr.2|) :=
        continuous_abs.measurable.comp ((hym.comp measurable_fst).sub (hcont_alpha.measurable.comp measurable_snd))
      exact (Measurable.ite ((hm1 (measurableSet_singleton 0)).union (hm2 (measurableSet_singleton 0))) measurable_const
        (((hm1.sub hm2).div (hm1.add hm2)).pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (e12Rat_bounds _ _ _ _).1, norm_one]
      exact (e12Rat_bounds _ _ _ _).2
  have hae_alpha_diff : ∀ᵐ pr : ℝ × ℝ ∂(lam0.prod lam0), alphaFn pr.1 ≠ alphaFn pr.2 := by
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards with t₁
      exact (alphaFn_ne_const_ae (alphaFn t₁)).mono fun t₂ ht₂ => Ne.symm ht₂
    · exact (isClosed_eq (hcont_alpha.comp continuous_fst) (hcont_alpha.comp continuous_snd)).measurableSet.compl
  have hae_alpha_u : ∀ᵐ pr : ℝ × ℝ ∂(lam0.prod lam0), alphaFn pr.1 ≠ u pr.2 := by
    have hm_au : MeasurableSet {pr : ℝ × ℝ | alphaFn pr.2 ≠ u pr.1} := by
      have hm1 : Measurable (fun pr : ℝ × ℝ => (alphaFn pr.2, u pr.1)) :=
        (hcont_alpha.measurable.comp measurable_snd).prodMk (hum.comp measurable_fst)
      exact (hm1 isClosed_diagonal.measurableSet).compl
    have hs : ∀ᵐ pr : ℝ × ℝ ∂(lam0.prod lam0), alphaFn pr.2 ≠ u pr.1 := by
      rw [Measure.ae_prod_iff_ae_ae hm_au]
      filter_upwards with t₂
      exact alphaFn_ne_const_ae (u t₂)
    exact (Measure.measurePreserving_swap : MeasurePreserving Prod.swap (lam0.prod lam0) (lam0.prod lam0)).quasiMeasurePreserving.ae hs
  have hae_y_alpha : ∀ᵐ pr : ℝ × ℝ ∂(lam0.prod lam0), y pr.1 ≠ alphaFn pr.2 := by
    have hm_ya : MeasurableSet {pr : ℝ × ℝ | y pr.1 ≠ alphaFn pr.2} := by
      have hm1 : Measurable (fun pr : ℝ × ℝ => (y pr.1, alphaFn pr.2)) :=
        (hym.comp measurable_fst).prodMk (hcont_alpha.measurable.comp measurable_snd)
      exact (hm1 isClosed_diagonal.measurableSet).compl
    rw [Measure.ae_prod_iff_ae_ae hm_ya]
    filter_upwards with t₁
    exact (alphaFn_ne_const_ae (y t₁)).mono fun t₂ ht₂ => Ne.symm ht₂
  have hterm_eq : ∀ (p q : Bool) (a b : Fin 14 × Fin 14),
      100000000 * ((lam0 (cell y u (p, a))).toReal * (lam0 (cell y u (q, b))).toReal *
        ((M_int (p, a) (q, b) : ℝ) / (100 * (getAt wxList a.1.1 : ℝ) * (getAt wxList b.1.1 : ℝ)))) =
      zVec y u (p, a) * zVec y u (q, b) * (M_int (p, a) (q, b) : ℝ) := by
    intro p q ⟨i, j⟩ ⟨i2, j2⟩
    have hwi : (getAt wxList i.1 : ℝ) ≠ 0 := by exact_mod_cast (wxList_pos i).ne'
    have hwi2 : (getAt wxList i2.1 : ℝ) ≠ 0 := by exact_mod_cast (wxList_pos i2).ne'
    dsimp [zVec]
    field_simp [hwi, hwi2]
    ring
  have h11 : ∑ a : Fin 14 × Fin 14, ∑ b : Fin 14 × Fin 14,
      zVec y u (false, a) * zVec y u (false, b) * (M_int (false, a) (false, b) : ℝ) ≤
      100000000 * ∫ pr : ℝ × ℝ, e1Rat (alphaFn pr.1) (y pr.1) (alphaFn pr.2) (y pr.2) ∂(lam0.prod lam0) := by
    have hp := integral_prod_partition_ge
      (A := fun a => cell y u (false, a)) (B := fun b => cell y u (false, b))
      (fun a => measurableSet_cell hym hum (false, a))
      (fun b => measurableSet_cell hym hum (false, b))
      (cell_disjoint_side y u false) (cell_disjoint_side y u false)
      hm_e1_y (fun pr => (e1Rat_bounds _ _ _ _).1)
      (S := {pr : ℝ × ℝ | alphaFn pr.1 ≠ alphaFn pr.2}) hae_alpha_diff
      (c := fun a b => (M_int (false, a) (false, b) : ℝ) /
        (100 * (getAt wxList a.1.1 : ℝ) * (getAt wxList b.1.1 : ℝ)))
      (fun a b => div_nonneg (by exact_mod_cast M_int_nonneg (false, a) (false, b))
        (by have := (wxList_pos a.1).le; have := (wxList_pos b.1).le; positivity))
      (fun ⟨i, j⟩ ⟨i2, j2⟩ t₁ ht₁ t₂ ht₂ hne => by
        exact e1Rat_ge_M1Int (alphaFn_mem_bucket i ht₁.1) (alphaFn_mem_bucket i2 ht₂.1)
          (yBucket_bounds ht₁.2) (yBucket_bounds ht₂.2) hne)
    calc ∑ a : Fin 14 × Fin 14, ∑ b : Fin 14 × Fin 14,
          zVec y u (false, a) * zVec y u (false, b) * (M_int (false, a) (false, b) : ℝ)
        = ∑ a : Fin 14 × Fin 14, ∑ b : Fin 14 × Fin 14,
            100000000 * ((lam0 (cell y u (false, a))).toReal * (lam0 (cell y u (false, b))).toReal *
              ((M_int (false, a) (false, b) : ℝ) / (100 * (getAt wxList a.1.1 : ℝ) * (getAt wxList b.1.1 : ℝ)))) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (hterm_eq false false a b).symm
      _ = 100000000 * ∑ a : Fin 14 × Fin 14, ∑ b : Fin 14 × Fin 14,
            (lam0 (cell y u (false, a))).toReal * (lam0 (cell y u (false, b))).toReal *
              ((M_int (false, a) (false, b) : ℝ) / (100 * (getAt wxList a.1.1 : ℝ) * (getAt wxList b.1.1 : ℝ))) := by
          simp_rw [← Finset.mul_sum]
      _ ≤ 100000000 * ∫ pr : ℝ × ℝ, e1Rat (alphaFn pr.1) (y pr.1) (alphaFn pr.2) (y pr.2) ∂(lam0.prod lam0) :=
          mul_le_mul_of_nonneg_left hp (by norm_num)
  have h22 : ∑ a : Fin 14 × Fin 14, ∑ b : Fin 14 × Fin 14,
      zVec y u (true, a) * zVec y u (true, b) * (M_int (true, a) (true, b) : ℝ) ≤
      100000000 * ∫ pr : ℝ × ℝ, e1Rat (alphaFn pr.1) (u pr.1) (alphaFn pr.2) (u pr.2) ∂(lam0.prod lam0) := by
    have hp := integral_prod_partition_ge
      (A := fun a => cell y u (true, a)) (B := fun b => cell y u (true, b))
      (fun a => measurableSet_cell hym hum (true, a))
      (fun b => measurableSet_cell hym hum (true, b))
      (cell_disjoint_side y u true) (cell_disjoint_side y u true)
      hm_e1_u (fun pr => (e1Rat_bounds _ _ _ _).1)
      (S := {pr : ℝ × ℝ | alphaFn pr.1 ≠ alphaFn pr.2}) hae_alpha_diff
      (c := fun a b => (M_int (true, a) (true, b) : ℝ) /
        (100 * (getAt wxList a.1.1 : ℝ) * (getAt wxList b.1.1 : ℝ)))
      (fun a b => div_nonneg (by exact_mod_cast M_int_nonneg (true, a) (true, b))
        (by have := (wxList_pos a.1).le; have := (wxList_pos b.1).le; positivity))
      (fun ⟨i, j⟩ ⟨i2, j2⟩ t₁ ht₁ t₂ ht₂ hne => by
        exact e1Rat_ge_M1Int (alphaFn_mem_bucket i ht₁.1) (alphaFn_mem_bucket i2 ht₂.1)
          (yBucket_bounds ht₁.2) (yBucket_bounds ht₂.2) hne)
    calc ∑ a : Fin 14 × Fin 14, ∑ b : Fin 14 × Fin 14,
          zVec y u (true, a) * zVec y u (true, b) * (M_int (true, a) (true, b) : ℝ)
        = 100000000 * ∑ a : Fin 14 × Fin 14, ∑ b : Fin 14 × Fin 14,
            (lam0 (cell y u (true, a))).toReal * (lam0 (cell y u (true, b))).toReal *
              ((M_int (true, a) (true, b) : ℝ) / (100 * (getAt wxList a.1.1 : ℝ) * (getAt wxList b.1.1 : ℝ))) := by
          simp_rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (hterm_eq true true a b).symm
      _ ≤ 100000000 * ∫ pr : ℝ × ℝ, e1Rat (alphaFn pr.1) (u pr.1) (alphaFn pr.2) (u pr.2) ∂(lam0.prod lam0) :=
          mul_le_mul_of_nonneg_left hp (by norm_num)
  have h12 : ∑ a : Fin 14 × Fin 14, ∑ b : Fin 14 × Fin 14,
      zVec y u (false, a) * zVec y u (true, b) * (M_int (false, a) (true, b) : ℝ) ≤
      100000000 * ∫ pr : ℝ × ℝ, e12Rat (alphaFn pr.1) (y pr.1) (u pr.2) (alphaFn pr.2) ∂(lam0.prod lam0) := by
    have hp := integral_prod_partition_ge
      (A := fun a => cell y u (false, a)) (B := fun b => cell y u (true, b))
      (fun a => measurableSet_cell hym hum (false, a))
      (fun b => measurableSet_cell hym hum (true, b))
      (cell_disjoint_side y u false) (cell_disjoint_side y u true)
      hm_e12 (fun pr => (e12Rat_bounds _ _ _ _).1)
      (S := {pr : ℝ × ℝ | alphaFn pr.1 ≠ u pr.2 ∧ y pr.1 ≠ alphaFn pr.2})
      (hae_alpha_u.and hae_y_alpha)
      (c := fun a b => (M_int (false, a) (true, b) : ℝ) /
        (100 * (getAt wxList a.1.1 : ℝ) * (getAt wxList b.1.1 : ℝ)))
      (fun a b => div_nonneg (by exact_mod_cast M_int_nonneg (false, a) (true, b))
        (by have := (wxList_pos a.1).le; have := (wxList_pos b.1).le; positivity))
      (fun ⟨i, j⟩ ⟨l, k⟩ t₁ ht₁ t₂ ht₂ hne => by
        exact e12Rat_ge_M12Int (alphaFn_mem_bucket i ht₁.1) (yBucket_bounds ht₁.2)
          (yBucket_bounds ht₂.2) (alphaFn_mem_bucket l ht₂.1) hne.1 hne.2)
    calc ∑ a : Fin 14 × Fin 14, ∑ b : Fin 14 × Fin 14,
          zVec y u (false, a) * zVec y u (true, b) * (M_int (false, a) (true, b) : ℝ)
        = 100000000 * ∑ a : Fin 14 × Fin 14, ∑ b : Fin 14 × Fin 14,
            (lam0 (cell y u (false, a))).toReal * (lam0 (cell y u (true, b))).toReal *
              ((M_int (false, a) (true, b) : ℝ) / (100 * (getAt wxList a.1.1 : ℝ) * (getAt wxList b.1.1 : ℝ))) := by
          simp_rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (hterm_eq false true a b).symm
      _ ≤ 100000000 * ∫ pr : ℝ × ℝ, e12Rat (alphaFn pr.1) (y pr.1) (u pr.2) (alphaFn pr.2) ∂(lam0.prod lam0) :=
          mul_le_mul_of_nonneg_left hp (by norm_num)
  have h21 : ∑ b : Fin 14 × Fin 14, ∑ a : Fin 14 × Fin 14,
      zVec y u (true, b) * zVec y u (false, a) * (M_int (true, b) (false, a) : ℝ) =
      ∑ a : Fin 14 × Fin 14, ∑ b : Fin 14 × Fin 14,
        zVec y u (false, a) * zVec y u (true, b) * (M_int (false, a) (true, b) : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ⟨i, j⟩ _ => Finset.sum_congr rfl fun ⟨l, k⟩ _ => ?_
    have hm : M_int (true, (l, k)) (false, (i, j)) = M_int (false, (i, j)) (true, (l, k)) := rfl
    rw [hm]
    ring
  have hsplit : ∑ a : Idx, ∑ b : Idx, zVec y u a * zVec y u b * (M_int a b : ℝ) =
      (∑ a : Fin 14 × Fin 14, ∑ b : Fin 14 × Fin 14,
        zVec y u (false, a) * zVec y u (false, b) * (M_int (false, a) (false, b) : ℝ)) +
      (∑ a : Fin 14 × Fin 14, ∑ b : Fin 14 × Fin 14,
        zVec y u (false, a) * zVec y u (true, b) * (M_int (false, a) (true, b) : ℝ)) +
      (∑ b : Fin 14 × Fin 14, ∑ a : Fin 14 × Fin 14,
        zVec y u (true, b) * zVec y u (false, a) * (M_int (true, b) (false, a) : ℝ)) +
      (∑ a : Fin 14 × Fin 14, ∑ b : Fin 14 × Fin 14,
        zVec y u (true, a) * zVec y u (true, b) * (M_int (true, a) (true, b) : ℝ)) := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib]
    ring
  unfold energyRat
  linarith

private def V0_g0 : List (List Int) := [
  [Int.negSucc 16, Int.negSucc 22, Int.negSucc 2, Int.ofNat 67, Int.ofNat 89, Int.ofNat 96, Int.ofNat 47, Int.negSucc 82, Int.ofNat 60, Int.ofNat 17, Int.negSucc 6, Int.ofNat 17, Int.ofNat 13, Int.ofNat 79, Int.ofNat 9, Int.ofNat 206, Int.negSucc 720],
  [Int.ofNat 27, Int.ofNat 7, Int.ofNat 14, Int.negSucc 15, Int.negSucc 60, Int.ofNat 80, Int.ofNat 116, Int.negSucc 72, Int.negSucc 44, Int.negSucc 29, Int.ofNat 42, Int.negSucc 53, Int.ofNat 5, Int.negSucc 25, Int.ofNat 24, Int.ofNat 164, Int.negSucc 746],
  [Int.ofNat 0, Int.ofNat 30, Int.negSucc 52, Int.negSucc 55, Int.negSucc 1, Int.negSucc 37, Int.ofNat 14, Int.negSucc 63, Int.negSucc 155, Int.negSucc 45, Int.ofNat 65, Int.ofNat 43, Int.negSucc 4, Int.negSucc 4, Int.ofNat 30, Int.ofNat 108, Int.negSucc 727],
  [Int.negSucc 10, Int.negSucc 5, Int.ofNat 7, Int.negSucc 6, Int.ofNat 27, Int.negSucc 103, Int.negSucc 30, Int.ofNat 71, Int.negSucc 104, Int.negSucc 13, Int.ofNat 68, Int.ofNat 30, Int.ofNat 4, Int.ofNat 150, Int.negSucc 8, Int.ofNat 126, Int.negSucc 697],
  [Int.negSucc 11, Int.negSucc 18, Int.ofNat 14, Int.negSucc 2, Int.ofNat 7, Int.negSucc 71, Int.negSucc 39, Int.ofNat 64, Int.negSucc 26, Int.ofNat 5, Int.negSucc 21, Int.ofNat 61, Int.ofNat 15, Int.ofNat 99, Int.negSucc 70, Int.ofNat 215, Int.negSucc 670],
  [Int.ofNat 23, Int.negSucc 33, Int.ofNat 10, Int.ofNat 6, Int.negSucc 23, Int.ofNat 4, Int.negSucc 41, Int.ofNat 47, Int.ofNat 77, Int.ofNat 49, Int.negSucc 44, Int.ofNat 67, Int.negSucc 24, Int.ofNat 76, Int.ofNat 41, Int.ofNat 261, Int.negSucc 662],
  [Int.negSucc 13, Int.ofNat 48, Int.ofNat 14, Int.ofNat 17, Int.negSucc 29, Int.ofNat 55, Int.negSucc 41, Int.ofNat 20, Int.ofNat 158, Int.ofNat 32, Int.negSucc 70, Int.ofNat 74, Int.ofNat 97, Int.ofNat 72, Int.ofNat 101, Int.ofNat 273, Int.negSucc 659]
]
private def V0_g1 : List (List Int) := [
  [Int.negSucc 5, Int.negSucc 4, Int.negSucc 5, Int.negSucc 62, Int.negSucc 80, Int.ofNat 48, Int.negSucc 161, Int.ofNat 49, Int.ofNat 89, Int.ofNat 19, Int.negSucc 45, Int.negSucc 104, Int.ofNat 9, Int.negSucc 118, Int.negSucc 9, Int.negSucc 89, Int.negSucc 150],
  [Int.negSucc 16, Int.negSucc 10, Int.negSucc 16, Int.negSucc 25, Int.ofNat 60, Int.ofNat 24, Int.negSucc 118, Int.ofNat 45, Int.ofNat 31, Int.negSucc 6, Int.negSucc 27, Int.negSucc 185, Int.ofNat 3, Int.negSucc 196, Int.negSucc 0, Int.negSucc 158, Int.negSucc 150],
  [Int.ofNat 11, Int.ofNat 0, Int.ofNat 7, Int.ofNat 46, Int.ofNat 74, Int.negSucc 13, Int.negSucc 102, Int.ofNat 18, Int.ofNat 19, Int.negSucc 8, Int.negSucc 7, Int.negSucc 148, Int.negSucc 2, Int.negSucc 218, Int.negSucc 6, Int.negSucc 204, Int.negSucc 144],
  [Int.ofNat 1, Int.ofNat 7, Int.ofNat 21, Int.ofNat 65, Int.negSucc 52, Int.negSucc 31, Int.negSucc 16, Int.ofNat 6, Int.negSucc 1, Int.negSucc 9, Int.negSucc 9, Int.negSucc 196, Int.negSucc 9, Int.negSucc 168, Int.negSucc 8, Int.negSucc 204, Int.negSucc 137],
  [Int.ofNat 4, Int.ofNat 6, Int.negSucc 5, Int.ofNat 50, Int.negSucc 56, Int.negSucc 1, Int.ofNat 30, Int.ofNat 17, Int.negSucc 27, Int.negSucc 14, Int.negSucc 21, Int.negSucc 206, Int.negSucc 4, Int.negSucc 193, Int.negSucc 29, Int.negSucc 163, Int.negSucc 141],
  [Int.negSucc 16, Int.ofNat 16, Int.ofNat 1, Int.negSucc 5, Int.ofNat 7, Int.ofNat 9, Int.ofNat 77, Int.negSucc 12, Int.negSucc 37, Int.ofNat 2, Int.ofNat 1, Int.negSucc 231, Int.negSucc 20, Int.negSucc 199, Int.ofNat 8, Int.negSucc 142, Int.negSucc 145],
  [Int.negSucc 0, Int.negSucc 16, Int.ofNat 12, Int.negSucc 59, Int.ofNat 34, Int.ofNat 1, Int.ofNat 89, Int.negSucc 49, Int.negSucc 30, Int.negSucc 24, Int.ofNat 13, Int.negSucc 262, Int.ofNat 23, Int.negSucc 207, Int.ofNat 27, Int.negSucc 139, Int.negSucc 143]
]
private def V0_g2 : List (List Int) := [
  [Int.ofNat 33, Int.ofNat 32, Int.negSucc 27, Int.ofNat 18, Int.ofNat 42, Int.negSucc 89, Int.ofNat 79, Int.ofNat 192, Int.ofNat 121, Int.ofNat 64, Int.negSucc 69, Int.ofNat 40, Int.negSucc 15, Int.negSucc 76, Int.ofNat 40, Int.negSucc 198, Int.negSucc 76],
  [Int.negSucc 9, Int.negSucc 15, Int.ofNat 20, Int.negSucc 14, Int.ofNat 1, Int.negSucc 21, Int.ofNat 115, Int.ofNat 138, Int.ofNat 71, Int.ofNat 38, Int.negSucc 10, Int.ofNat 69, Int.negSucc 29, Int.negSucc 135, Int.ofNat 39, Int.negSucc 290, Int.negSucc 48],
  [Int.negSucc 34, Int.negSucc 14, Int.ofNat 22, Int.negSucc 5, Int.negSucc 20, Int.ofNat 7, Int.ofNat 53, Int.ofNat 62, Int.ofNat 56, Int.ofNat 34, Int.ofNat 9, Int.ofNat 174, Int.negSucc 44, Int.negSucc 157, Int.ofNat 42, Int.negSucc 350, Int.negSucc 28],
  [Int.negSucc 10, Int.negSucc 21, Int.negSucc 10, Int.ofNat 4, Int.negSucc 44, Int.ofNat 52, Int.ofNat 26, Int.negSucc 3, Int.ofNat 30, Int.ofNat 11, Int.ofNat 10, Int.ofNat 190, Int.negSucc 40, Int.negSucc 153, Int.ofNat 39, Int.negSucc 365, Int.negSucc 30],
  [Int.ofNat 11, Int.negSucc 1, Int.negSucc 42, Int.ofNat 16, Int.negSucc 3, Int.ofNat 63, Int.negSucc 11, Int.negSucc 39, Int.negSucc 22, Int.negSucc 10, Int.ofNat 14, Int.ofNat 184, Int.negSucc 34, Int.negSucc 189, Int.ofNat 27, Int.negSucc 351, Int.negSucc 37],
  [Int.ofNat 1, Int.ofNat 28, Int.ofNat 5, Int.negSucc 4, Int.ofNat 14, Int.ofNat 7, Int.negSucc 52, Int.negSucc 68, Int.negSucc 55, Int.negSucc 27, Int.ofNat 48, Int.ofNat 186, Int.negSucc 52, Int.negSucc 199, Int.ofNat 49, Int.negSucc 342, Int.negSucc 36],
  [Int.ofNat 17, Int.ofNat 3, Int.ofNat 37, Int.negSucc 4, Int.ofNat 38, Int.negSucc 18, Int.negSucc 58, Int.negSucc 66, Int.negSucc 72, Int.negSucc 37, Int.ofNat 80, Int.ofNat 209, Int.negSucc 22, Int.negSucc 215, Int.ofNat 61, Int.negSucc 345, Int.negSucc 33]
]
private def V0_g3 : List (List Int) := [
  [Int.ofNat 2, Int.ofNat 14, Int.ofNat 35, Int.ofNat 13, Int.negSucc 10, Int.negSucc 127, Int.negSucc 7, Int.negSucc 198, Int.negSucc 2, Int.ofNat 0, Int.negSucc 229, Int.ofNat 26, Int.negSucc 0, Int.ofNat 79, Int.ofNat 25, Int.negSucc 164, Int.ofNat 0],
  [Int.negSucc 1, Int.negSucc 25, Int.negSucc 5, Int.ofNat 24, Int.negSucc 27, Int.negSucc 27, Int.ofNat 6, Int.negSucc 149, Int.negSucc 6, Int.negSucc 9, Int.negSucc 181, Int.negSucc 16, Int.negSucc 3, Int.ofNat 155, Int.ofNat 6, Int.negSucc 235, Int.ofNat 48],
  [Int.ofNat 3, Int.ofNat 0, Int.negSucc 34, Int.negSucc 0, Int.ofNat 15, Int.ofNat 42, Int.negSucc 18, Int.negSucc 66, Int.ofNat 35, Int.ofNat 8, Int.negSucc 89, Int.negSucc 26, Int.negSucc 11, Int.ofNat 259, Int.ofNat 3, Int.negSucc 277, Int.ofNat 81],
  [Int.ofNat 5, Int.ofNat 9, Int.ofNat 5, Int.negSucc 23, Int.ofNat 24, Int.ofNat 81, Int.ofNat 1, Int.negSucc 14, Int.ofNat 30, Int.ofNat 6, Int.negSucc 15, Int.negSucc 46, Int.negSucc 9, Int.ofNat 350, Int.ofNat 4, Int.negSucc 301, Int.ofNat 88],
  [Int.ofNat 9, Int.ofNat 22, Int.ofNat 5, Int.negSucc 11, Int.ofNat 25, Int.ofNat 44, Int.ofNat 3, Int.ofNat 17, Int.ofNat 5, Int.ofNat 1, Int.ofNat 47, Int.negSucc 50, Int.negSucc 9, Int.ofNat 376, Int.negSucc 5, Int.negSucc 311, Int.ofNat 92],
  [Int.ofNat 4, Int.negSucc 3, Int.ofNat 10, Int.ofNat 0, Int.negSucc 9, Int.negSucc 6, Int.ofNat 7, Int.ofNat 57, Int.negSucc 9, Int.negSucc 12, Int.ofNat 81, Int.negSucc 54, Int.negSucc 23, Int.ofNat 385, Int.ofNat 11, Int.negSucc 320, Int.ofNat 98],
  [Int.negSucc 18, Int.negSucc 4, Int.ofNat 1, Int.ofNat 11, Int.negSucc 24, Int.negSucc 33, Int.negSucc 5, Int.ofNat 68, Int.negSucc 31, Int.negSucc 14, Int.ofNat 90, Int.negSucc 61, Int.negSucc 5, Int.ofNat 406, Int.ofNat 20, Int.negSucc 330, Int.ofNat 103]
]
private def V0_g4 : List (List Int) := [
  [Int.negSucc 22, Int.negSucc 12, Int.negSucc 8, Int.ofNat 29, Int.negSucc 26, Int.negSucc 57, Int.negSucc 24, Int.negSucc 98, Int.ofNat 50, Int.ofNat 110, Int.ofNat 335, Int.negSucc 23, Int.negSucc 10, Int.negSucc 1, Int.negSucc 177, Int.ofNat 85, Int.ofNat 108],
  [Int.ofNat 37, Int.ofNat 11, Int.ofNat 9, Int.ofNat 32, Int.negSucc 7, Int.ofNat 10, Int.negSucc 10, Int.negSucc 52, Int.ofNat 55, Int.ofNat 99, Int.ofNat 196, Int.negSucc 34, Int.negSucc 4, Int.negSucc 20, Int.negSucc 255, Int.ofNat 92, Int.ofNat 154],
  [Int.ofNat 5, Int.ofNat 16, Int.ofNat 2, Int.negSucc 16, Int.ofNat 15, Int.ofNat 15, Int.ofNat 1, Int.negSucc 16, Int.ofNat 52, Int.ofNat 43, Int.ofNat 50, Int.ofNat 7, Int.ofNat 27, Int.negSucc 40, Int.negSucc 345, Int.ofNat 115, Int.ofNat 189],
  [Int.negSucc 5, Int.ofNat 13, Int.ofNat 54, Int.negSucc 43, Int.ofNat 18, Int.ofNat 11, Int.ofNat 26, Int.negSucc 12, Int.ofNat 26, Int.ofNat 13, Int.negSucc 18, Int.ofNat 32, Int.ofNat 62, Int.negSucc 27, Int.negSucc 416, Int.ofNat 147, Int.ofNat 204],
  [Int.negSucc 3, Int.ofNat 3, Int.ofNat 11, Int.negSucc 25, Int.ofNat 10, Int.ofNat 6, Int.ofNat 3, Int.ofNat 1, Int.negSucc 8, Int.negSucc 18, Int.negSucc 63, Int.ofNat 31, Int.ofNat 76, Int.negSucc 35, Int.negSucc 461, Int.ofNat 164, Int.ofNat 215],
  [Int.ofNat 0, Int.negSucc 16, Int.negSucc 24, Int.ofNat 5, Int.negSucc 8, Int.negSucc 4, Int.ofNat 11, Int.ofNat 27, Int.negSucc 23, Int.negSucc 20, Int.negSucc 87, Int.ofNat 36, Int.ofNat 82, Int.negSucc 35, Int.negSucc 482, Int.ofNat 168, Int.ofNat 225],
  [Int.negSucc 10, Int.ofNat 0, Int.negSucc 33, Int.ofNat 35, Int.negSucc 3, Int.ofNat 8, Int.ofNat 10, Int.ofNat 29, Int.negSucc 43, Int.negSucc 33, Int.negSucc 98, Int.ofNat 39, Int.ofNat 93, Int.negSucc 35, Int.negSucc 500, Int.ofNat 175, Int.ofNat 229]
]
private def V0_g5 : List (List Int) := [
  [Int.negSucc 12, Int.ofNat 1, Int.ofNat 9, Int.ofNat 42, Int.ofNat 14, Int.ofNat 46, Int.ofNat 11, Int.ofNat 55, Int.negSucc 42, Int.negSucc 320, Int.ofNat 43, Int.ofNat 24, Int.negSucc 48, Int.ofNat 13, Int.ofNat 40, Int.ofNat 153, Int.ofNat 165],
  [Int.ofNat 17, Int.ofNat 15, Int.ofNat 27, Int.ofNat 15, Int.negSucc 29, Int.ofNat 1, Int.negSucc 31, Int.ofNat 65, Int.ofNat 17, Int.negSucc 252, Int.ofNat 22, Int.ofNat 5, Int.negSucc 104, Int.negSucc 5, Int.ofNat 70, Int.ofNat 183, Int.ofNat 201],
  [Int.negSucc 9, Int.ofNat 1, Int.negSucc 26, Int.negSucc 23, Int.negSucc 7, Int.negSucc 16, Int.negSucc 0, Int.ofNat 22, Int.ofNat 0, Int.negSucc 93, Int.ofNat 4, Int.ofNat 0, Int.negSucc 201, Int.negSucc 12, Int.ofNat 121, Int.ofNat 212, Int.ofNat 235],
  [Int.ofNat 22, Int.negSucc 34, Int.ofNat 5, Int.negSucc 8, Int.ofNat 2, Int.negSucc 14, Int.negSucc 2, Int.negSucc 16, Int.ofNat 3, Int.negSucc 14, Int.negSucc 1, Int.negSucc 4, Int.negSucc 264, Int.negSucc 9, Int.ofNat 150, Int.ofNat 251, Int.ofNat 254],
  [Int.ofNat 22, Int.negSucc 17, Int.negSucc 6, Int.ofNat 9, Int.ofNat 9, Int.ofNat 8, Int.negSucc 0, Int.negSucc 2, Int.negSucc 0, Int.ofNat 55, Int.negSucc 13, Int.negSucc 10, Int.negSucc 307, Int.negSucc 18, Int.ofNat 165, Int.ofNat 276, Int.ofNat 271],
  [Int.negSucc 4, Int.ofNat 17, Int.negSucc 8, Int.ofNat 0, Int.ofNat 8, Int.ofNat 3, Int.ofNat 7, Int.negSucc 20, Int.ofNat 6, Int.ofNat 95, Int.negSucc 29, Int.negSucc 9, Int.negSucc 342, Int.negSucc 21, Int.ofNat 178, Int.ofNat 291, Int.ofNat 279],
  [Int.negSucc 39, Int.ofNat 26, Int.ofNat 13, Int.negSucc 4, Int.ofNat 9, Int.ofNat 9, Int.ofNat 10, Int.negSucc 24, Int.ofNat 13, Int.ofNat 91, Int.negSucc 34, Int.negSucc 9, Int.negSucc 365, Int.negSucc 24, Int.ofNat 184, Int.ofNat 298, Int.ofNat 281]
]
private def V0_g6 : List (List Int) := [
  [Int.negSucc 10, Int.negSucc 5, Int.ofNat 30, Int.ofNat 28, Int.negSucc 0, Int.ofNat 89, Int.negSucc 22, Int.ofNat 91, Int.negSucc 241, Int.ofNat 143, Int.negSucc 50, Int.ofNat 12, Int.ofNat 126, Int.ofNat 1, Int.ofNat 122, Int.ofNat 92, Int.ofNat 191],
  [Int.ofNat 23, Int.ofNat 9, Int.ofNat 15, Int.ofNat 4, Int.negSucc 2, Int.ofNat 33, Int.negSucc 27, Int.ofNat 66, Int.negSucc 154, Int.ofNat 139, Int.negSucc 48, Int.ofNat 2, Int.ofNat 167, Int.negSucc 14, Int.ofNat 162, Int.ofNat 111, Int.ofNat 214],
  [Int.ofNat 4, Int.negSucc 13, Int.negSucc 20, Int.negSucc 6, Int.negSucc 15, Int.negSucc 31, Int.ofNat 16, Int.ofNat 39, Int.negSucc 59, Int.ofNat 49, Int.negSucc 9, Int.ofNat 12, Int.ofNat 190, Int.negSucc 15, Int.ofNat 202, Int.ofNat 117, Int.ofNat 234],
  [Int.negSucc 24, Int.ofNat 16, Int.negSucc 13, Int.ofNat 32, Int.negSucc 8, Int.negSucc 27, Int.ofNat 5, Int.negSucc 22, Int.negSucc 1, Int.ofNat 24, Int.ofNat 18, Int.ofNat 6, Int.ofNat 254, Int.negSucc 20, Int.ofNat 234, Int.ofNat 137, Int.ofNat 248],
  [Int.negSucc 7, Int.ofNat 20, Int.negSucc 10, Int.ofNat 11, Int.ofNat 2, Int.negSucc 8, Int.ofNat 7, Int.negSucc 16, Int.ofNat 40, Int.negSucc 16, Int.ofNat 18, Int.ofNat 5, Int.ofNat 291, Int.negSucc 30, Int.ofNat 267, Int.ofNat 158, Int.ofNat 263],
  [Int.ofNat 11, Int.negSucc 11, Int.negSucc 8, Int.negSucc 21, Int.ofNat 6, Int.negSucc 10, Int.ofNat 10, Int.negSucc 37, Int.ofNat 75, Int.negSucc 38, Int.ofNat 26, Int.ofNat 2, Int.ofNat 320, Int.negSucc 34, Int.ofNat 287, Int.ofNat 169, Int.ofNat 269],
  [Int.ofNat 0, Int.negSucc 17, Int.ofNat 19, Int.negSucc 22, Int.ofNat 22, Int.negSucc 1, Int.ofNat 9, Int.negSucc 51, Int.ofNat 94, Int.negSucc 48, Int.ofNat 38, Int.negSucc 0, Int.ofNat 335, Int.negSucc 38, Int.ofNat 293, Int.ofNat 175, Int.ofNat 269]
]
private def V0 : List (List Int) := V0_g0 ++ V0_g1 ++ V0_g2 ++ V0_g3 ++ V0_g4 ++ V0_g5 ++ V0_g6

private def V1_g0 : List (List Int) := [
  [Int.negSucc 11, Int.negSucc 8, Int.ofNat 12, Int.ofNat 4, Int.ofNat 75, Int.negSucc 11, Int.negSucc 2, Int.negSucc 57, Int.ofNat 11, Int.negSucc 290, Int.negSucc 172, Int.ofNat 15, Int.negSucc 37, Int.ofNat 5, Int.negSucc 297, Int.negSucc 134, Int.ofNat 203, Int.negSucc 278],
  [Int.ofNat 4, Int.ofNat 24, Int.ofNat 33, Int.negSucc 50, Int.negSucc 70, Int.ofNat 0, Int.negSucc 1, Int.ofNat 13, Int.ofNat 4, Int.negSucc 172, Int.negSucc 87, Int.negSucc 69, Int.negSucc 4, Int.ofNat 98, Int.negSucc 129, Int.negSucc 130, Int.ofNat 270, Int.negSucc 359],
  [Int.ofNat 5, Int.ofNat 6, Int.negSucc 20, Int.ofNat 57, Int.ofNat 27, Int.negSucc 27, Int.negSucc 85, Int.negSucc 30, Int.ofNat 27, Int.negSucc 60, Int.negSucc 27, Int.ofNat 25, Int.ofNat 17, Int.ofNat 162, Int.ofNat 29, Int.negSucc 130, Int.ofNat 350, Int.negSucc 464],
  [Int.negSucc 7, Int.ofNat 11, Int.negSucc 2, Int.negSucc 7, Int.negSucc 47, Int.negSucc 8, Int.negSucc 22, Int.ofNat 48, Int.ofNat 16, Int.ofNat 23, Int.ofNat 15, Int.negSucc 39, Int.ofNat 0, Int.ofNat 56, Int.ofNat 132, Int.negSucc 88, Int.ofNat 383, Int.negSucc 564],
  [Int.ofNat 10, Int.negSucc 38, Int.negSucc 3, Int.negSucc 22, Int.negSucc 6, Int.negSucc 0, Int.ofNat 5, Int.ofNat 43, Int.negSucc 18, Int.ofNat 77, Int.ofNat 1, Int.negSucc 54, Int.ofNat 18, Int.ofNat 107, Int.ofNat 119, Int.ofNat 4, Int.ofNat 320, Int.negSucc 645],
  [Int.negSucc 27, Int.negSucc 39, Int.ofNat 4, Int.ofNat 1, Int.ofNat 9, Int.ofNat 22, Int.ofNat 8, Int.ofNat 8, Int.negSucc 21, Int.ofNat 70, Int.ofNat 46, Int.negSucc 72, Int.negSucc 18, Int.ofNat 117, Int.ofNat 139, Int.negSucc 62, Int.ofNat 227, Int.negSucc 705],
  [Int.ofNat 26, Int.ofNat 44, Int.negSucc 4, Int.ofNat 17, Int.ofNat 28, Int.ofNat 38, Int.ofNat 40, Int.negSucc 50, Int.negSucc 2, Int.ofNat 83, Int.ofNat 73, Int.negSucc 94, Int.ofNat 106, Int.ofNat 93, Int.ofNat 157, Int.negSucc 93, Int.ofNat 197, Int.negSucc 724]
]
private def V1_g1 : List (List Int) := [
  [Int.ofNat 6, Int.negSucc 12, Int.ofNat 30, Int.ofNat 80, Int.negSucc 101, Int.ofNat 93, Int.negSucc 4, Int.negSucc 9, Int.negSucc 1, Int.ofNat 40, Int.ofNat 22, Int.ofNat 117, Int.negSucc 31, Int.negSucc 133, Int.negSucc 153, Int.negSucc 3, Int.ofNat 13, Int.negSucc 97],
  [Int.ofNat 4, Int.negSucc 27, Int.negSucc 8, Int.negSucc 3, Int.ofNat 46, Int.ofNat 147, Int.ofNat 41, Int.ofNat 21, Int.negSucc 7, Int.ofNat 84, Int.ofNat 38, Int.ofNat 96, Int.negSucc 33, Int.negSucc 128, Int.negSucc 118, Int.ofNat 9, Int.ofNat 26, Int.negSucc 153],
  [Int.ofNat 2, Int.ofNat 18, Int.ofNat 20, Int.negSucc 60, Int.ofNat 5, Int.ofNat 91, Int.ofNat 29, Int.ofNat 21, Int.negSucc 6, Int.ofNat 61, Int.ofNat 27, Int.ofNat 189, Int.negSucc 32, Int.negSucc 134, Int.negSucc 76, Int.ofNat 8, Int.ofNat 49, Int.negSucc 208],
  [Int.negSucc 17, Int.ofNat 20, Int.ofNat 4, Int.ofNat 1, Int.ofNat 57, Int.ofNat 22, Int.ofNat 25, Int.ofNat 17, Int.ofNat 18, Int.ofNat 7, Int.ofNat 14, Int.ofNat 212, Int.negSucc 37, Int.negSucc 196, Int.negSucc 51, Int.ofNat 37, Int.ofNat 68, Int.negSucc 248],
  [Int.negSucc 25, Int.ofNat 36, Int.negSucc 25, Int.ofNat 18, Int.ofNat 8, Int.negSucc 27, Int.ofNat 10, Int.negSucc 14, Int.ofNat 4, Int.ofNat 2, Int.negSucc 21, Int.ofNat 227, Int.negSucc 27, Int.negSucc 172, Int.negSucc 54, Int.ofNat 69, Int.ofNat 53, Int.negSucc 281],
  [Int.ofNat 19, Int.ofNat 14, Int.negSucc 19, Int.ofNat 2, Int.negSucc 16, Int.negSucc 89, Int.ofNat 15, Int.negSucc 6, Int.negSucc 10, Int.ofNat 2, Int.ofNat 3, Int.ofNat 244, Int.negSucc 37, Int.negSucc 169, Int.negSucc 46, Int.ofNat 42, Int.ofNat 20, Int.negSucc 301],
  [Int.ofNat 14, Int.negSucc 47, Int.ofNat 19, Int.negSucc 14, Int.negSucc 34, Int.negSucc 105, Int.ofNat 25, Int.ofNat 10, Int.ofNat 15, Int.negSucc 7, Int.negSucc 7, Int.ofNat 272, Int.ofNat 10, Int.negSucc 184, Int.negSucc 41, Int.ofNat 30, Int.ofNat 2, Int.negSucc 308]
]
private def V1_g2 : List (List Int) := [
  [Int.ofNat 20, Int.ofNat 6, Int.ofNat 4, Int.negSucc 49, Int.ofNat 31, Int.negSucc 48, Int.negSucc 227, Int.negSucc 73, Int.ofNat 24, Int.ofNat 152, Int.ofNat 90, Int.negSucc 13, Int.negSucc 17, Int.negSucc 109, Int.negSucc 127, Int.ofNat 66, Int.negSucc 57, Int.negSucc 123],
  [Int.negSucc 41, Int.ofNat 20, Int.negSucc 9, Int.negSucc 15, Int.negSucc 21, Int.negSucc 12, Int.negSucc 134, Int.negSucc 84, Int.negSucc 12, Int.ofNat 106, Int.ofNat 40, Int.negSucc 102, Int.negSucc 33, Int.negSucc 139, Int.negSucc 161, Int.ofNat 80, Int.negSucc 78, Int.negSucc 151],
  [Int.ofNat 9, Int.negSucc 18, Int.ofNat 24, Int.ofNat 60, Int.ofNat 25, Int.negSucc 35, Int.negSucc 75, Int.negSucc 56, Int.negSucc 3, Int.ofNat 42, Int.ofNat 5, Int.negSucc 118, Int.negSucc 41, Int.negSucc 169, Int.negSucc 177, Int.ofNat 96, Int.negSucc 82, Int.negSucc 179],
  [Int.ofNat 15, Int.negSucc 2, Int.ofNat 38, Int.ofNat 2, Int.negSucc 2, Int.ofNat 1, Int.negSucc 4, Int.negSucc 27, Int.negSucc 5, Int.negSucc 36, Int.negSucc 13, Int.negSucc 157, Int.negSucc 68, Int.negSucc 245, Int.negSucc 172, Int.ofNat 119, Int.negSucc 78, Int.negSucc 209],
  [Int.ofNat 12, Int.ofNat 32, Int.ofNat 16, Int.ofNat 12, Int.negSucc 22, Int.ofNat 0, Int.ofNat 35, Int.ofNat 8, Int.ofNat 4, Int.negSucc 27, Int.negSucc 20, Int.negSucc 148, Int.negSucc 73, Int.negSucc 256, Int.negSucc 179, Int.ofNat 152, Int.negSucc 98, Int.negSucc 235],
  [Int.ofNat 6, Int.ofNat 0, Int.negSucc 23, Int.negSucc 4, Int.ofNat 0, Int.ofNat 13, Int.ofNat 69, Int.ofNat 32, Int.negSucc 28, Int.negSucc 35, Int.negSucc 12, Int.negSucc 152, Int.negSucc 80, Int.negSucc 266, Int.negSucc 178, Int.ofNat 135, Int.negSucc 121, Int.negSucc 248],
  [Int.negSucc 11, Int.negSucc 25, Int.negSucc 60, Int.negSucc 20, Int.negSucc 1, Int.ofNat 0, Int.ofNat 78, Int.ofNat 42, Int.negSucc 14, Int.negSucc 20, Int.negSucc 33, Int.negSucc 177, Int.negSucc 53, Int.negSucc 292, Int.negSucc 180, Int.ofNat 128, Int.negSucc 136, Int.negSucc 250]
]
private def V1_g3 : List (List Int) := [
  [Int.negSucc 3, Int.ofNat 0, Int.ofNat 20, Int.ofNat 38, Int.ofNat 28, Int.negSucc 50, Int.negSucc 3, Int.ofNat 250, Int.ofNat 158, Int.ofNat 5, Int.ofNat 197, Int.negSucc 31, Int.ofNat 4, Int.ofNat 27, Int.negSucc 120, Int.ofNat 22, Int.negSucc 111, Int.negSucc 104],
  [Int.negSucc 3, Int.ofNat 10, Int.ofNat 3, Int.negSucc 23, Int.negSucc 5, Int.negSucc 28, Int.ofNat 58, Int.ofNat 157, Int.ofNat 99, Int.negSucc 34, Int.ofNat 140, Int.negSucc 43, Int.ofNat 19, Int.ofNat 118, Int.negSucc 195, Int.ofNat 10, Int.negSucc 150, Int.negSucc 109],
  [Int.negSucc 4, Int.ofNat 22, Int.negSucc 22, Int.ofNat 5, Int.ofNat 0, Int.negSucc 19, Int.ofNat 38, Int.ofNat 63, Int.ofNat 43, Int.negSucc 0, Int.ofNat 66, Int.ofNat 30, Int.ofNat 42, Int.ofNat 201, Int.negSucc 252, Int.ofNat 5, Int.negSucc 174, Int.negSucc 116],
  [Int.ofNat 8, Int.ofNat 6, Int.ofNat 13, Int.negSucc 22, Int.ofNat 0, Int.ofNat 28, Int.ofNat 29, Int.negSucc 11, Int.negSucc 4, Int.ofNat 13, Int.ofNat 14, Int.ofNat 33, Int.ofNat 45, Int.ofNat 227, Int.negSucc 298, Int.ofNat 26, Int.negSucc 197, Int.negSucc 136],
  [Int.negSucc 3, Int.negSucc 8, Int.ofNat 19, Int.negSucc 14, Int.ofNat 15, Int.ofNat 13, Int.ofNat 4, Int.negSucc 49, Int.negSucc 30, Int.ofNat 20, Int.negSucc 9, Int.ofNat 37, Int.ofNat 52, Int.ofNat 260, Int.negSucc 339, Int.ofNat 55, Int.negSucc 232, Int.negSucc 153],
  [Int.ofNat 6, Int.negSucc 7, Int.negSucc 7, Int.ofNat 7, Int.negSucc 13, Int.ofNat 5, Int.negSucc 6, Int.negSucc 58, Int.negSucc 37, Int.ofNat 37, Int.negSucc 30, Int.ofNat 42, Int.ofNat 48, Int.ofNat 268, Int.negSucc 351, Int.ofNat 51, Int.negSucc 258, Int.negSucc 162],
  [Int.negSucc 2, Int.negSucc 6, Int.negSucc 25, Int.ofNat 21, Int.negSucc 17, Int.negSucc 0, Int.negSucc 8, Int.negSucc 45, Int.negSucc 62, Int.ofNat 57, Int.negSucc 25, Int.ofNat 45, Int.ofNat 75, Int.ofNat 276, Int.negSucc 366, Int.ofNat 51, Int.negSucc 276, Int.negSucc 160]
]
private def V1_g4 : List (List Int) := [
  [Int.ofNat 10, Int.ofNat 19, Int.ofNat 37, Int.ofNat 23, Int.ofNat 48, Int.negSucc 24, Int.ofNat 61, Int.ofNat 122, Int.negSucc 60, Int.ofNat 234, Int.negSucc 277, Int.negSucc 33, Int.ofNat 11, Int.negSucc 12, Int.negSucc 54, Int.negSucc 206, Int.negSucc 16, Int.ofNat 17],
  [Int.negSucc 4, Int.ofNat 1, Int.ofNat 3, Int.negSucc 18, Int.negSucc 26, Int.negSucc 61, Int.ofNat 39, Int.ofNat 57, Int.negSucc 25, Int.ofNat 151, Int.negSucc 183, Int.negSucc 35, Int.negSucc 1, Int.negSucc 12, Int.negSucc 78, Int.negSucc 300, Int.negSucc 21, Int.ofNat 37],
  [Int.negSucc 0, Int.negSucc 14, Int.negSucc 50, Int.negSucc 3, Int.negSucc 12, Int.negSucc 20, Int.ofNat 10, Int.ofNat 21, Int.negSucc 5, Int.ofNat 73, Int.negSucc 51, Int.negSucc 13, Int.negSucc 32, Int.negSucc 38, Int.negSucc 70, Int.negSucc 409, Int.negSucc 12, Int.ofNat 44],
  [Int.negSucc 33, Int.ofNat 22, Int.negSucc 4, Int.ofNat 9, Int.negSucc 22, Int.ofNat 24, Int.negSucc 8, Int.negSucc 19, Int.ofNat 9, Int.ofNat 17, Int.ofNat 13, Int.negSucc 6, Int.negSucc 64, Int.negSucc 66, Int.negSucc 81, Int.negSucc 480, Int.negSucc 20, Int.ofNat 48],
  [Int.negSucc 11, Int.ofNat 18, Int.ofNat 13, Int.ofNat 10, Int.ofNat 0, Int.ofNat 4, Int.negSucc 17, Int.negSucc 25, Int.ofNat 26, Int.negSucc 14, Int.ofNat 71, Int.negSucc 4, Int.negSucc 77, Int.negSucc 72, Int.negSucc 97, Int.negSucc 522, Int.negSucc 42, Int.ofNat 55],
  [Int.ofNat 1, Int.negSucc 6, Int.ofNat 13, Int.negSucc 0, Int.ofNat 3, Int.ofNat 4, Int.negSucc 6, Int.negSucc 18, Int.ofNat 9, Int.negSucc 30, Int.ofNat 112, Int.negSucc 3, Int.negSucc 78, Int.negSucc 74, Int.negSucc 101, Int.negSucc 552, Int.negSucc 54, Int.ofNat 62],
  [Int.ofNat 42, Int.negSucc 29, Int.negSucc 14, Int.negSucc 13, Int.ofNat 15, Int.ofNat 14, Int.negSucc 14, Int.negSucc 20, Int.ofNat 13, Int.negSucc 34, Int.ofNat 94, Int.negSucc 3, Int.negSucc 80, Int.negSucc 79, Int.negSucc 99, Int.negSucc 575, Int.negSucc 62, Int.ofNat 67]
]
private def V1_g5 : List (List Int) := [
  [Int.negSucc 17, Int.ofNat 9, Int.ofNat 31, Int.negSucc 10, Int.ofNat 25, Int.negSucc 36, Int.ofNat 80, Int.negSucc 12, Int.negSucc 296, Int.ofNat 12, Int.ofNat 177, Int.negSucc 15, Int.ofNat 31, Int.negSucc 20, Int.negSucc 75, Int.negSucc 11, Int.ofNat 213, Int.ofNat 109],
  [Int.ofNat 5, Int.negSucc 2, Int.ofNat 3, Int.ofNat 17, Int.negSucc 1, Int.negSucc 61, Int.ofNat 33, Int.ofNat 9, Int.negSucc 240, Int.negSucc 17, Int.ofNat 124, Int.negSucc 20, Int.ofNat 82, Int.negSucc 18, Int.negSucc 102, Int.negSucc 18, Int.ofNat 260, Int.ofNat 144],
  [Int.negSucc 2, Int.negSucc 10, Int.negSucc 35, Int.ofNat 16, Int.negSucc 7, Int.ofNat 8, Int.ofNat 29, Int.ofNat 5, Int.negSucc 89, Int.negSucc 9, Int.ofNat 48, Int.negSucc 8, Int.ofNat 174, Int.negSucc 39, Int.negSucc 134, Int.ofNat 3, Int.ofNat 318, Int.ofNat 168],
  [Int.ofNat 23, Int.ofNat 23, Int.negSucc 7, Int.negSucc 8, Int.negSucc 6, Int.ofNat 9, Int.negSucc 8, Int.ofNat 3, Int.negSucc 8, Int.ofNat 5, Int.ofNat 22, Int.ofNat 0, Int.ofNat 237, Int.negSucc 64, Int.negSucc 163, Int.ofNat 14, Int.ofNat 349, Int.ofNat 192],
  [Int.ofNat 27, Int.ofNat 5, Int.ofNat 1, Int.negSucc 11, Int.ofNat 3, Int.ofNat 4, Int.negSucc 2, Int.ofNat 11, Int.ofNat 59, Int.ofNat 25, Int.negSucc 9, Int.negSucc 7, Int.ofNat 280, Int.negSucc 77, Int.negSucc 185, Int.ofNat 11, Int.ofNat 363, Int.ofNat 213],
  [Int.negSucc 10, Int.negSucc 11, Int.ofNat 1, Int.ofNat 1, Int.negSucc 5, Int.ofNat 7, Int.negSucc 19, Int.ofNat 12, Int.ofNat 81, Int.ofNat 31, Int.negSucc 20, Int.negSucc 13, Int.ofNat 316, Int.negSucc 86, Int.negSucc 197, Int.ofNat 11, Int.ofNat 375, Int.ofNat 226],
  [Int.negSucc 25, Int.negSucc 12, Int.ofNat 4, Int.ofNat 0, Int.ofNat 5, Int.ofNat 19, Int.negSucc 40, Int.ofNat 26, Int.ofNat 102, Int.ofNat 21, Int.negSucc 30, Int.negSucc 12, Int.ofNat 337, Int.negSucc 91, Int.negSucc 202, Int.ofNat 14, Int.ofNat 377, Int.ofNat 231]
]
private def V1_g6 : List (List Int) := [
  [Int.negSucc 5, Int.ofNat 1, Int.ofNat 19, Int.ofNat 4, Int.negSucc 3, Int.negSucc 37, Int.ofNat 170, Int.negSucc 195, Int.ofNat 151, Int.ofNat 106, Int.ofNat 74, Int.negSucc 39, Int.negSucc 107, Int.ofNat 35, Int.negSucc 56, Int.ofNat 42, Int.ofNat 215, Int.ofNat 104],
  [Int.negSucc 3, Int.ofNat 4, Int.negSucc 13, Int.negSucc 5, Int.ofNat 3, Int.negSucc 45, Int.ofNat 107, Int.negSucc 127, Int.ofNat 144, Int.ofNat 68, Int.ofNat 33, Int.negSucc 31, Int.negSucc 152, Int.ofNat 57, Int.negSucc 76, Int.ofNat 50, Int.ofNat 253, Int.ofNat 129],
  [Int.ofNat 27, Int.ofNat 9, Int.negSucc 16, Int.ofNat 13, Int.ofNat 10, Int.ofNat 5, Int.ofNat 48, Int.negSucc 46, Int.ofNat 45, Int.ofNat 21, Int.ofNat 8, Int.negSucc 7, Int.negSucc 189, Int.ofNat 61, Int.negSucc 102, Int.ofNat 69, Int.ofNat 280, Int.ofNat 152],
  [Int.negSucc 10, Int.negSucc 29, Int.ofNat 30, Int.negSucc 8, Int.ofNat 6, Int.ofNat 1, Int.negSucc 10, Int.ofNat 7, Int.ofNat 27, Int.ofNat 25, Int.negSucc 6, Int.ofNat 5, Int.negSucc 253, Int.ofNat 64, Int.negSucc 120, Int.ofNat 84, Int.ofNat 302, Int.ofNat 167],
  [Int.negSucc 13, Int.negSucc 15, Int.ofNat 11, Int.negSucc 7, Int.ofNat 3, Int.negSucc 7, Int.negSucc 32, Int.ofNat 58, Int.ofNat 1, Int.ofNat 30, Int.negSucc 9, Int.ofNat 10, Int.negSucc 293, Int.ofNat 73, Int.negSucc 136, Int.ofNat 93, Int.ofNat 322, Int.ofNat 184],
  [Int.negSucc 0, Int.ofNat 6, Int.negSucc 14, Int.ofNat 3, Int.negSucc 3, Int.ofNat 9, Int.negSucc 48, Int.ofNat 73, Int.negSucc 44, Int.ofNat 15, Int.negSucc 2, Int.ofNat 14, Int.negSucc 322, Int.ofNat 79, Int.negSucc 146, Int.ofNat 103, Int.ofNat 337, Int.ofNat 198],
  [Int.ofNat 19, Int.ofNat 23, Int.negSucc 25, Int.ofNat 3, Int.negSucc 11, Int.ofNat 32, Int.negSucc 63, Int.ofNat 82, Int.negSucc 42, Int.ofNat 7, Int.negSucc 23, Int.ofNat 19, Int.negSucc 339, Int.ofNat 84, Int.negSucc 147, Int.ofNat 105, Int.ofNat 339, Int.ofNat 203]
]
private def V1 : List (List Int) := V1_g0 ++ V1_g1 ++ V1_g2 ++ V1_g3 ++ V1_g4 ++ V1_g5 ++ V1_g6

private def V2_g0 : List (List Int) := [
  [Int.ofNat 13, Int.negSucc 14, Int.negSucc 12, Int.ofNat 7, Int.ofNat 54, Int.ofNat 30, Int.ofNat 106, Int.negSucc 95, Int.negSucc 20, Int.ofNat 3, Int.ofNat 37, Int.ofNat 3, Int.ofNat 138, Int.negSucc 119, Int.ofNat 134, Int.negSucc 176],
  [Int.negSucc 7, Int.ofNat 5, Int.ofNat 1, Int.negSucc 5, Int.negSucc 36, Int.ofNat 4, Int.ofNat 32, Int.negSucc 79, Int.negSucc 26, Int.ofNat 178, Int.ofNat 49, Int.negSucc 9, Int.ofNat 180, Int.negSucc 128, Int.ofNat 100, Int.negSucc 123],
  [Int.negSucc 0, Int.ofNat 19, Int.negSucc 0, Int.ofNat 6, Int.negSucc 7, Int.negSucc 34, Int.negSucc 66, Int.ofNat 75, Int.ofNat 28, Int.ofNat 159, Int.negSucc 124, Int.negSucc 15, Int.ofNat 119, Int.negSucc 126, Int.ofNat 94, Int.negSucc 134],
  [Int.negSucc 15, Int.ofNat 11, Int.ofNat 7, Int.ofNat 2, Int.ofNat 42, Int.negSucc 21, Int.negSucc 74, Int.ofNat 16, Int.ofNat 8, Int.negSucc 56, Int.negSucc 155, Int.negSucc 4, Int.ofNat 66, Int.negSucc 104, Int.ofNat 86, Int.negSucc 172],
  [Int.negSucc 21, Int.negSucc 2, Int.ofNat 10, Int.negSucc 16, Int.negSucc 9, Int.ofNat 19, Int.ofNat 14, Int.negSucc 12, Int.ofNat 4, Int.negSucc 154, Int.negSucc 154, Int.ofNat 2, Int.ofNat 28, Int.negSucc 57, Int.ofNat 54, Int.negSucc 178],
  [Int.negSucc 0, Int.ofNat 0, Int.negSucc 25, Int.ofNat 0, Int.negSucc 61, Int.ofNat 69, Int.ofNat 34, Int.negSucc 23, Int.ofNat 6, Int.negSucc 140, Int.negSucc 117, Int.negSucc 2, Int.ofNat 30, Int.negSucc 34, Int.ofNat 26, Int.negSucc 122],
  [Int.ofNat 36, Int.ofNat 2, Int.negSucc 12, Int.ofNat 9, Int.negSucc 21, Int.ofNat 34, Int.ofNat 29, Int.ofNat 3, Int.negSucc 55, Int.negSucc 43, Int.negSucc 46, Int.negSucc 11, Int.ofNat 16, Int.negSucc 6, Int.ofNat 10, Int.negSucc 40]
]
private def V2_g1 : List (List Int) := [
  [Int.negSucc 6, Int.negSucc 28, Int.ofNat 14, Int.negSucc 14, Int.negSucc 55, Int.ofNat 66, Int.ofNat 67, Int.ofNat 182, Int.ofNat 48, Int.ofNat 1, Int.ofNat 103, Int.ofNat 4, Int.negSucc 58, Int.ofNat 11, Int.ofNat 3, Int.negSucc 28],
  [Int.negSucc 22, Int.ofNat 3, Int.negSucc 3, Int.negSucc 10, Int.ofNat 46, Int.ofNat 51, Int.negSucc 10, Int.ofNat 137, Int.ofNat 50, Int.negSucc 45, Int.ofNat 127, Int.ofNat 6, Int.negSucc 40, Int.ofNat 3, Int.ofNat 19, Int.negSucc 30],
  [Int.ofNat 0, Int.ofNat 19, Int.negSucc 21, Int.ofNat 29, Int.ofNat 62, Int.ofNat 7, Int.negSucc 40, Int.ofNat 43, Int.ofNat 20, Int.negSucc 103, Int.ofNat 126, Int.ofNat 6, Int.negSucc 0, Int.negSucc 14, Int.ofNat 40, Int.negSucc 41],
  [Int.ofNat 15, Int.negSucc 0, Int.negSucc 5, Int.ofNat 2, Int.ofNat 5, Int.negSucc 47, Int.negSucc 35, Int.negSucc 40, Int.negSucc 33, Int.negSucc 94, Int.ofNat 166, Int.ofNat 1, Int.negSucc 15, Int.negSucc 32, Int.ofNat 38, Int.negSucc 56],
  [Int.ofNat 2, Int.ofNat 3, Int.ofNat 11, Int.negSucc 20, Int.negSucc 57, Int.negSucc 65, Int.negSucc 9, Int.negSucc 52, Int.negSucc 43, Int.negSucc 37, Int.ofNat 165, Int.ofNat 3, Int.negSucc 9, Int.ofNat 0, Int.ofNat 21, Int.negSucc 68],
  [Int.negSucc 18, Int.ofNat 2, Int.ofNat 1, Int.ofNat 4, Int.negSucc 80, Int.negSucc 43, Int.ofNat 10, Int.negSucc 52, Int.negSucc 29, Int.negSucc 2, Int.ofNat 132, Int.ofNat 4, Int.negSucc 11, Int.negSucc 8, Int.negSucc 5, Int.negSucc 51],
  [Int.negSucc 7, Int.ofNat 7, Int.negSucc 0, Int.ofNat 10, Int.negSucc 25, Int.negSucc 15, Int.ofNat 10, Int.negSucc 14, Int.negSucc 27, Int.ofNat 0, Int.ofNat 43, Int.negSucc 13, Int.negSucc 0, Int.negSucc 2, Int.negSucc 5, Int.negSucc 17]
]
private def V2_g2 : List (List Int) := [
  [Int.negSucc 31, Int.ofNat 17, Int.negSucc 13, Int.negSucc 33, Int.ofNat 19, Int.ofNat 75, Int.negSucc 109, Int.negSucc 99, Int.negSucc 22, Int.ofNat 57, Int.ofNat 28, Int.ofNat 2, Int.negSucc 200, Int.ofNat 144, Int.negSucc 99, Int.ofNat 37],
  [Int.negSucc 0, Int.ofNat 12, Int.ofNat 11, Int.negSucc 3, Int.ofNat 31, Int.ofNat 43, Int.ofNat 14, Int.negSucc 85, Int.negSucc 23, Int.ofNat 44, Int.negSucc 53, Int.ofNat 5, Int.negSucc 240, Int.ofNat 116, Int.negSucc 71, Int.ofNat 4],
  [Int.ofNat 7, Int.negSucc 13, Int.ofNat 0, Int.negSucc 16, Int.ofNat 26, Int.ofNat 30, Int.ofNat 70, Int.negSucc 43, Int.negSucc 15, Int.negSucc 2, Int.negSucc 45, Int.ofNat 3, Int.negSucc 207, Int.ofNat 66, Int.negSucc 32, Int.negSucc 11],
  [Int.ofNat 7, Int.negSucc 24, Int.ofNat 6, Int.ofNat 15, Int.negSucc 30, Int.negSucc 10, Int.ofNat 59, Int.ofNat 7, Int.ofNat 10, Int.ofNat 51, Int.negSucc 49, Int.ofNat 4, Int.negSucc 201, Int.ofNat 45, Int.negSucc 17, Int.negSucc 25],
  [Int.ofNat 13, Int.negSucc 17, Int.negSucc 6, Int.ofNat 22, Int.negSucc 41, Int.negSucc 38, Int.ofNat 17, Int.ofNat 50, Int.ofNat 21, Int.ofNat 96, Int.negSucc 48, Int.negSucc 0, Int.negSucc 147, Int.ofNat 63, Int.negSucc 22, Int.negSucc 32],
  [Int.ofNat 11, Int.ofNat 34, Int.negSucc 24, Int.ofNat 19, Int.negSucc 28, Int.negSucc 50, Int.negSucc 5, Int.ofNat 64, Int.ofNat 17, Int.ofNat 78, Int.negSucc 32, Int.negSucc 0, Int.negSucc 105, Int.ofNat 41, Int.negSucc 48, Int.negSucc 25],
  [Int.ofNat 12, Int.ofNat 15, Int.negSucc 0, Int.ofNat 5, Int.negSucc 15, Int.negSucc 19, Int.negSucc 14, Int.ofNat 24, Int.negSucc 3, Int.ofNat 30, Int.negSucc 21, Int.negSucc 19, Int.negSucc 45, Int.ofNat 16, Int.negSucc 23, Int.negSucc 1]
]
private def V2_g3 : List (List Int) := [
  [Int.negSucc 8, Int.ofNat 12, Int.negSucc 25, Int.ofNat 42, Int.ofNat 70, Int.negSucc 132, Int.ofNat 62, Int.ofNat 7, Int.ofNat 6, Int.negSucc 66, Int.negSucc 27, Int.ofNat 6, Int.ofNat 40, Int.ofNat 260, Int.negSucc 266, Int.ofNat 173],
  [Int.negSucc 3, Int.negSucc 9, Int.ofNat 20, Int.negSucc 4, Int.negSucc 21, Int.negSucc 12, Int.ofNat 39, Int.negSucc 8, Int.ofNat 1, Int.negSucc 16, Int.negSucc 78, Int.negSucc 2, Int.ofNat 155, Int.ofNat 281, Int.negSucc 264, Int.ofNat 137],
  [Int.negSucc 3, Int.ofNat 13, Int.ofNat 1, Int.negSucc 17, Int.negSucc 52, Int.ofNat 63, Int.ofNat 32, Int.ofNat 6, Int.ofNat 0, Int.negSucc 4, Int.ofNat 14, Int.negSucc 3, Int.ofNat 191, Int.ofNat 257, Int.negSucc 212, Int.ofNat 95],
  [Int.negSucc 1, Int.ofNat 27, Int.negSucc 13, Int.negSucc 25, Int.negSucc 30, Int.ofNat 53, Int.negSucc 0, Int.ofNat 2, Int.negSucc 5, Int.ofNat 50, Int.ofNat 26, Int.negSucc 2, Int.ofNat 140, Int.ofNat 188, Int.negSucc 148, Int.ofNat 50],
  [Int.ofNat 6, Int.negSucc 25, Int.negSucc 9, Int.ofNat 7, Int.ofNat 39, Int.ofNat 49, Int.negSucc 77, Int.ofNat 5, Int.ofNat 2, Int.ofNat 64, Int.ofNat 34, Int.negSucc 7, Int.ofNat 113, Int.ofNat 143, Int.negSucc 109, Int.ofNat 20],
  [Int.ofNat 24, Int.negSucc 52, Int.ofNat 13, Int.ofNat 1, Int.ofNat 65, Int.ofNat 21, Int.negSucc 79, Int.negSucc 6, Int.negSucc 2, Int.ofNat 32, Int.ofNat 13, Int.negSucc 4, Int.ofNat 72, Int.ofNat 80, Int.negSucc 98, Int.ofNat 18],
  [Int.ofNat 11, Int.negSucc 23, Int.ofNat 10, Int.ofNat 1, Int.ofNat 21, Int.ofNat 6, Int.negSucc 34, Int.negSucc 3, Int.ofNat 1, Int.ofNat 5, Int.ofNat 2, Int.negSucc 10, Int.ofNat 26, Int.ofNat 22, Int.negSucc 33, Int.ofNat 7]
]
private def V2_g4 : List (List Int) := [
  [Int.ofNat 33, Int.ofNat 28, Int.ofNat 70, Int.ofNat 48, Int.negSucc 63, Int.ofNat 37, Int.negSucc 76, Int.negSucc 15, Int.ofNat 0, Int.negSucc 81, Int.negSucc 12, Int.negSucc 4, Int.negSucc 19, Int.negSucc 189, Int.negSucc 143, Int.ofNat 356],
  [Int.negSucc 30, Int.negSucc 36, Int.negSucc 46, Int.negSucc 11, Int.negSucc 41, Int.negSucc 17, Int.negSucc 29, Int.negSucc 16, Int.ofNat 4, Int.negSucc 15, Int.negSucc 44, Int.negSucc 2, Int.negSucc 1, Int.negSucc 279, Int.negSucc 151, Int.ofNat 358],
  [Int.ofNat 12, Int.negSucc 23, Int.negSucc 41, Int.ofNat 23, Int.ofNat 7, Int.ofNat 18, Int.ofNat 9, Int.negSucc 6, Int.negSucc 5, Int.ofNat 25, Int.ofNat 16, Int.ofNat 8, Int.ofNat 14, Int.negSucc 290, Int.negSucc 136, Int.ofNat 326],
  [Int.negSucc 10, Int.ofNat 24, Int.negSucc 3, Int.negSucc 11, Int.ofNat 33, Int.ofNat 16, Int.ofNat 60, Int.negSucc 1, Int.ofNat 4, Int.ofNat 43, Int.ofNat 14, Int.ofNat 8, Int.negSucc 5, Int.negSucc 233, Int.negSucc 98, Int.ofNat 248],
  [Int.negSucc 17, Int.ofNat 25, Int.ofNat 29, Int.negSucc 39, Int.ofNat 69, Int.ofNat 1, Int.ofNat 61, Int.ofNat 20, Int.ofNat 9, Int.ofNat 30, Int.ofNat 8, Int.ofNat 6, Int.ofNat 18, Int.negSucc 165, Int.negSucc 67, Int.ofNat 168],
  [Int.ofNat 10, Int.ofNat 9, Int.ofNat 35, Int.negSucc 59, Int.ofNat 45, Int.negSucc 8, Int.ofNat 59, Int.ofNat 11, Int.negSucc 0, Int.ofNat 11, Int.negSucc 5, Int.ofNat 4, Int.ofNat 3, Int.negSucc 110, Int.negSucc 39, Int.ofNat 104],
  [Int.negSucc 0, Int.negSucc 1, Int.ofNat 10, Int.negSucc 25, Int.ofNat 16, Int.negSucc 1, Int.ofNat 25, Int.ofNat 3, Int.negSucc 2, Int.ofNat 2, Int.negSucc 2, Int.ofNat 0, Int.negSucc 1, Int.negSucc 27, Int.negSucc 8, Int.ofNat 30]
]
private def V2_g5 : List (List Int) := [
  [Int.ofNat 32, Int.ofNat 14, Int.negSucc 46, Int.negSucc 109, Int.negSucc 11, Int.negSucc 20, Int.negSucc 30, Int.ofNat 58, Int.negSucc 110, Int.negSucc 34, Int.negSucc 40, Int.negSucc 20, Int.negSucc 3, Int.ofNat 107, Int.ofNat 283, Int.ofNat 267],
  [Int.negSucc 46, Int.negSucc 28, Int.ofNat 19, Int.ofNat 16, Int.negSucc 23, Int.negSucc 25, Int.negSucc 15, Int.negSucc 1, Int.negSucc 41, Int.negSucc 12, Int.negSucc 34, Int.negSucc 64, Int.ofNat 14, Int.ofNat 137, Int.ofNat 340, Int.ofNat 277],
  [Int.ofNat 11, Int.negSucc 13, Int.ofNat 30, Int.ofNat 3, Int.ofNat 16, Int.negSucc 24, Int.ofNat 14, Int.negSucc 14, Int.ofNat 6, Int.ofNat 18, Int.ofNat 7, Int.negSucc 95, Int.ofNat 23, Int.ofNat 129, Int.ofNat 337, Int.ofNat 265],
  [Int.ofNat 9, Int.ofNat 16, Int.ofNat 14, Int.ofNat 30, Int.ofNat 15, Int.ofNat 27, Int.ofNat 24, Int.negSucc 17, Int.ofNat 50, Int.ofNat 17, Int.ofNat 5, Int.negSucc 79, Int.ofNat 5, Int.ofNat 111, Int.ofNat 286, Int.ofNat 216],
  [Int.negSucc 12, Int.ofNat 11, Int.negSucc 20, Int.ofNat 48, Int.ofNat 9, Int.ofNat 53, Int.ofNat 25, Int.negSucc 19, Int.ofNat 58, Int.ofNat 8, Int.ofNat 12, Int.negSucc 64, Int.ofNat 12, Int.ofNat 77, Int.ofNat 219, Int.ofNat 147],
  [Int.ofNat 2, Int.ofNat 24, Int.negSucc 33, Int.ofNat 47, Int.negSucc 4, Int.ofNat 42, Int.ofNat 15, Int.negSucc 12, Int.ofNat 44, Int.ofNat 4, Int.ofNat 12, Int.negSucc 42, Int.ofNat 12, Int.ofNat 32, Int.ofNat 127, Int.ofNat 80],
  [Int.negSucc 3, Int.ofNat 13, Int.negSucc 17, Int.ofNat 20, Int.negSucc 0, Int.ofNat 17, Int.ofNat 4, Int.negSucc 5, Int.ofNat 11, Int.ofNat 0, Int.ofNat 4, Int.negSucc 15, Int.ofNat 2, Int.ofNat 8, Int.ofNat 38, Int.ofNat 25]
]
private def V2_g6 : List (List Int) := [
  [Int.ofNat 37, Int.negSucc 6, Int.negSucc 15, Int.negSucc 34, Int.negSucc 14, Int.negSucc 7, Int.negSucc 13, Int.negSucc 68, Int.ofNat 225, Int.negSucc 14, Int.ofNat 1, Int.ofNat 158, Int.ofNat 3, Int.ofNat 39, Int.ofNat 82, Int.ofNat 64],
  [Int.negSucc 16, Int.ofNat 3, Int.negSucc 5, Int.negSucc 19, Int.negSucc 24, Int.negSucc 25, Int.negSucc 7, Int.negSucc 35, Int.ofNat 113, Int.negSucc 8, Int.negSucc 1, Int.ofNat 247, Int.ofNat 11, Int.ofNat 42, Int.ofNat 96, Int.ofNat 68],
  [Int.negSucc 22, Int.negSucc 1, Int.ofNat 24, Int.negSucc 2, Int.ofNat 5, Int.negSucc 9, Int.negSucc 4, Int.ofNat 7, Int.ofNat 0, Int.ofNat 11, Int.ofNat 2, Int.ofNat 327, Int.ofNat 20, Int.ofNat 30, Int.ofNat 86, Int.ofNat 58],
  [Int.ofNat 22, Int.ofNat 8, Int.ofNat 5, Int.ofNat 25, Int.ofNat 12, Int.ofNat 13, Int.ofNat 10, Int.ofNat 25, Int.negSucc 81, Int.ofNat 15, Int.negSucc 8, Int.ofNat 267, Int.ofNat 10, Int.ofNat 30, Int.ofNat 82, Int.ofNat 57],
  [Int.ofNat 3, Int.negSucc 4, Int.negSucc 19, Int.ofNat 44, Int.ofNat 11, Int.ofNat 29, Int.ofNat 14, Int.ofNat 24, Int.negSucc 115, Int.ofNat 12, Int.negSucc 13, Int.ofNat 210, Int.ofNat 7, Int.ofNat 22, Int.ofNat 59, Int.ofNat 42],
  [Int.negSucc 4, Int.ofNat 2, Int.ofNat 3, Int.ofNat 25, Int.negSucc 0, Int.ofNat 33, Int.negSucc 0, Int.ofNat 18, Int.negSucc 88, Int.ofNat 9, Int.negSucc 8, Int.ofNat 132, Int.ofNat 0, Int.ofNat 12, Int.ofNat 39, Int.ofNat 23],
  [Int.negSucc 3, Int.ofNat 3, Int.negSucc 1, Int.ofNat 2, Int.negSucc 0, Int.ofNat 12, Int.negSucc 5, Int.ofNat 7, Int.negSucc 32, Int.ofNat 2, Int.negSucc 3, Int.ofNat 46, Int.negSucc 1, Int.ofNat 3, Int.ofNat 14, Int.ofNat 9]
]
private def V2 : List (List Int) := V2_g0 ++ V2_g1 ++ V2_g2 ++ V2_g3 ++ V2_g4 ++ V2_g5 ++ V2_g6

private def V3_g0 : List (List Int) := [
  [Int.negSucc 20, Int.ofNat 6, Int.ofNat 12, Int.negSucc 3, Int.negSucc 4, Int.negSucc 6, Int.ofNat 4, Int.negSucc 37, Int.negSucc 156, Int.negSucc 13, Int.negSucc 58, Int.negSucc 11, Int.negSucc 128, Int.ofNat 208, Int.ofNat 192, Int.ofNat 187, Int.ofNat 639],
  [Int.ofNat 26, Int.ofNat 16, Int.ofNat 20, Int.ofNat 1, Int.negSucc 17, Int.negSucc 0, Int.ofNat 30, Int.negSucc 14, Int.ofNat 0, Int.ofNat 7, Int.ofNat 95, Int.negSucc 8, Int.negSucc 124, Int.ofNat 127, Int.ofNat 97, Int.ofNat 110, Int.ofNat 676],
  [Int.negSucc 13, Int.negSucc 40, Int.negSucc 57, Int.ofNat 2, Int.negSucc 14, Int.ofNat 24, Int.ofNat 19, Int.ofNat 47, Int.negSucc 20, Int.negSucc 18, Int.ofNat 38, Int.negSucc 1, Int.negSucc 104, Int.ofNat 78, Int.ofNat 32, Int.ofNat 39, Int.ofNat 576],
  [Int.ofNat 17, Int.negSucc 0, Int.ofNat 21, Int.ofNat 21, Int.ofNat 41, Int.negSucc 2, Int.ofNat 17, Int.negSucc 15, Int.ofNat 47, Int.ofNat 18, Int.ofNat 98, Int.ofNat 0, Int.negSucc 68, Int.ofNat 31, Int.negSucc 8, Int.negSucc 23, Int.ofNat 438],
  [Int.negSucc 16, Int.ofNat 43, Int.ofNat 21, Int.negSucc 7, Int.ofNat 13, Int.negSucc 15, Int.negSucc 30, Int.ofNat 46, Int.ofNat 80, Int.ofNat 4, Int.ofNat 94, Int.ofNat 1, Int.negSucc 52, Int.ofNat 40, Int.ofNat 10, Int.negSucc 44, Int.ofNat 313],
  [Int.negSucc 5, Int.negSucc 9, Int.ofNat 12, Int.negSucc 1, Int.ofNat 11, Int.negSucc 14, Int.negSucc 106, Int.ofNat 34, Int.ofNat 51, Int.ofNat 2, Int.ofNat 78, Int.negSucc 2, Int.negSucc 42, Int.ofNat 37, Int.ofNat 43, Int.negSucc 24, Int.ofNat 189],
  [Int.ofNat 40, Int.negSucc 25, Int.negSucc 4, Int.ofNat 9, Int.ofNat 5, Int.ofNat 0, Int.negSucc 60, Int.ofNat 19, Int.ofNat 11, Int.ofNat 61, Int.ofNat 26, Int.negSucc 11, Int.negSucc 15, Int.ofNat 1, Int.ofNat 16, Int.negSucc 4, Int.ofNat 59]
]
private def V3_g1 : List (List Int) := [
  [Int.negSucc 1, Int.negSucc 30, Int.negSucc 15, Int.ofNat 8, Int.ofNat 42, Int.ofNat 29, Int.ofNat 31, Int.negSucc 74, Int.ofNat 213, Int.ofNat 31, Int.negSucc 93, Int.ofNat 5, Int.ofNat 71, Int.ofNat 43, Int.ofNat 65, Int.ofNat 70, Int.ofNat 347],
  [Int.negSucc 17, Int.ofNat 25, Int.negSucc 11, Int.negSucc 26, Int.negSucc 42, Int.negSucc 26, Int.negSucc 33, Int.negSucc 17, Int.ofNat 134, Int.ofNat 18, Int.negSucc 147, Int.ofNat 10, Int.ofNat 97, Int.ofNat 12, Int.ofNat 43, Int.ofNat 52, Int.ofNat 326],
  [Int.ofNat 18, Int.negSucc 11, Int.ofNat 52, Int.ofNat 7, Int.negSucc 46, Int.negSucc 29, Int.negSucc 29, Int.ofNat 10, Int.ofNat 26, Int.ofNat 5, Int.negSucc 178, Int.ofNat 2, Int.ofNat 89, Int.negSucc 24, Int.ofNat 24, Int.ofNat 21, Int.ofNat 256],
  [Int.ofNat 7, Int.ofNat 16, Int.negSucc 35, Int.negSucc 5, Int.negSucc 3, Int.negSucc 6, Int.negSucc 15, Int.ofNat 6, Int.negSucc 36, Int.negSucc 21, Int.negSucc 197, Int.ofNat 4, Int.ofNat 39, Int.negSucc 38, Int.negSucc 19, Int.negSucc 18, Int.ofNat 185],
  [Int.ofNat 7, Int.negSucc 16, Int.ofNat 1, Int.ofNat 33, Int.ofNat 29, Int.negSucc 1, Int.ofNat 3, Int.ofNat 7, Int.negSucc 69, Int.negSucc 20, Int.negSucc 175, Int.ofNat 2, Int.ofNat 33, Int.negSucc 14, Int.negSucc 16, Int.negSucc 33, Int.ofNat 130],
  [Int.ofNat 0, Int.negSucc 3, Int.ofNat 29, Int.negSucc 14, Int.ofNat 47, Int.ofNat 41, Int.ofNat 30, Int.negSucc 6, Int.negSucc 65, Int.negSucc 6, Int.negSucc 126, Int.negSucc 6, Int.ofNat 24, Int.negSucc 12, Int.ofNat 11, Int.negSucc 27, Int.ofNat 79],
  [Int.negSucc 8, Int.ofNat 15, Int.ofNat 13, Int.negSucc 5, Int.ofNat 19, Int.ofNat 26, Int.ofNat 12, Int.ofNat 2, Int.negSucc 18, Int.ofNat 16, Int.negSucc 44, Int.negSucc 17, Int.ofNat 9, Int.negSucc 8, Int.ofNat 6, Int.negSucc 12, Int.ofNat 23]
]
private def V3_g2 : List (List Int) := [
  [Int.ofNat 7, Int.ofNat 29, Int.negSucc 45, Int.ofNat 10, Int.ofNat 20, Int.ofNat 19, Int.negSucc 11, Int.ofNat 186, Int.negSucc 11, Int.negSucc 34, Int.ofNat 41, Int.ofNat 9, Int.ofNat 184, Int.negSucc 81, Int.negSucc 17, Int.ofNat 48, Int.ofNat 306],
  [Int.ofNat 22, Int.negSucc 6, Int.ofNat 33, Int.ofNat 18, Int.ofNat 41, Int.negSucc 13, Int.negSucc 32, Int.ofNat 44, Int.negSucc 49, Int.negSucc 15, Int.ofNat 30, Int.ofNat 15, Int.ofNat 283, Int.negSucc 87, Int.negSucc 14, Int.ofNat 54, Int.ofNat 274],
  [Int.negSucc 15, Int.negSucc 3, Int.negSucc 11, Int.negSucc 35, Int.negSucc 5, Int.ofNat 5, Int.ofNat 0, Int.negSucc 33, Int.negSucc 61, Int.negSucc 6, Int.ofNat 74, Int.ofNat 19, Int.ofNat 287, Int.negSucc 77, Int.negSucc 8, Int.ofNat 52, Int.ofNat 242],
  [Int.negSucc 15, Int.negSucc 19, Int.ofNat 21, Int.negSucc 16, Int.negSucc 34, Int.ofNat 18, Int.ofNat 27, Int.negSucc 51, Int.negSucc 20, Int.ofNat 14, Int.ofNat 83, Int.ofNat 13, Int.ofNat 196, Int.negSucc 82, Int.negSucc 30, Int.ofNat 19, Int.ofNat 185],
  [Int.ofNat 8, Int.negSucc 5, Int.ofNat 2, Int.negSucc 4, Int.negSucc 33, Int.ofNat 7, Int.ofNat 45, Int.negSucc 72, Int.negSucc 5, Int.ofNat 22, Int.ofNat 84, Int.ofNat 12, Int.ofNat 147, Int.negSucc 54, Int.negSucc 35, Int.negSucc 23, Int.ofNat 120],
  [Int.negSucc 13, Int.ofNat 19, Int.negSucc 14, Int.ofNat 28, Int.negSucc 3, Int.negSucc 27, Int.ofNat 47, Int.negSucc 71, Int.ofNat 17, Int.ofNat 21, Int.ofNat 59, Int.ofNat 9, Int.ofNat 108, Int.negSucc 55, Int.negSucc 12, Int.negSucc 22, Int.ofNat 65],
  [Int.negSucc 9, Int.ofNat 2, Int.negSucc 2, Int.ofNat 24, Int.negSucc 5, Int.negSucc 13, Int.ofNat 12, Int.negSucc 21, Int.ofNat 0, Int.ofNat 15, Int.ofNat 30, Int.negSucc 12, Int.ofNat 49, Int.negSucc 25, Int.negSucc 5, Int.negSucc 10, Int.ofNat 16]
]
private def V3_g3 : List (List Int) := [
  [Int.ofNat 26, Int.ofNat 14, Int.negSucc 22, Int.negSucc 5, Int.negSucc 20, Int.negSucc 37, Int.negSucc 83, Int.negSucc 123, Int.negSucc 62, Int.ofNat 33, Int.ofNat 39, Int.negSucc 6, Int.negSucc 77, Int.negSucc 275, Int.negSucc 195, Int.negSucc 51, Int.ofNat 225],
  [Int.negSucc 17, Int.ofNat 31, Int.negSucc 2, Int.negSucc 12, Int.ofNat 38, Int.ofNat 5, Int.ofNat 0, Int.negSucc 48, Int.negSucc 11, Int.ofNat 5, Int.negSucc 53, Int.negSucc 5, Int.negSucc 109, Int.negSucc 337, Int.negSucc 203, Int.negSucc 22, Int.ofNat 212],
  [Int.ofNat 6, Int.negSucc 24, Int.ofNat 3, Int.ofNat 45, Int.ofNat 26, Int.ofNat 22, Int.ofNat 50, Int.ofNat 1, Int.ofNat 12, Int.negSucc 1, Int.ofNat 10, Int.negSucc 5, Int.negSucc 81, Int.negSucc 337, Int.negSucc 173, Int.ofNat 0, Int.ofNat 200],
  [Int.negSucc 7, Int.ofNat 0, Int.ofNat 24, Int.negSucc 9, Int.negSucc 5, Int.ofNat 10, Int.ofNat 15, Int.ofNat 52, Int.ofNat 33, Int.negSucc 15, Int.negSucc 14, Int.negSucc 7, Int.negSucc 97, Int.negSucc 290, Int.negSucc 157, Int.negSucc 13, Int.ofNat 158],
  [Int.negSucc 26, Int.negSucc 13, Int.ofNat 1, Int.negSucc 16, Int.negSucc 39, Int.ofNat 6, Int.ofNat 4, Int.ofNat 71, Int.ofNat 14, Int.negSucc 16, Int.negSucc 12, Int.negSucc 2, Int.negSucc 72, Int.negSucc 175, Int.negSucc 114, Int.negSucc 36, Int.ofNat 109],
  [Int.negSucc 2, Int.negSucc 34, Int.ofNat 17, Int.negSucc 6, Int.negSucc 69, Int.negSucc 10, Int.ofNat 8, Int.ofNat 79, Int.ofNat 5, Int.negSucc 19, Int.negSucc 3, Int.ofNat 0, Int.negSucc 49, Int.negSucc 119, Int.negSucc 59, Int.negSucc 45, Int.ofNat 49],
  [Int.ofNat 6, Int.negSucc 11, Int.ofNat 4, Int.negSucc 2, Int.negSucc 28, Int.negSucc 2, Int.ofNat 3, Int.ofNat 37, Int.ofNat 1, Int.negSucc 10, Int.negSucc 0, Int.negSucc 9, Int.negSucc 15, Int.negSucc 35, Int.negSucc 18, Int.negSucc 16, Int.ofNat 15]
]
private def V3_g4 : List (List Int) := [
  [Int.ofNat 29, Int.negSucc 8, Int.ofNat 1, Int.negSucc 91, Int.ofNat 42, Int.negSucc 50, Int.ofNat 75, Int.ofNat 34, Int.ofNat 8, Int.negSucc 4, Int.negSucc 0, Int.ofNat 2, Int.negSucc 15, Int.ofNat 134, Int.negSucc 225, Int.negSucc 323, Int.ofNat 140],
  [Int.ofNat 6, Int.ofNat 42, Int.negSucc 11, Int.ofNat 38, Int.negSucc 30, Int.ofNat 23, Int.ofNat 27, Int.negSucc 0, Int.negSucc 1, Int.ofNat 7, Int.negSucc 42, Int.ofNat 5, Int.ofNat 28, Int.ofNat 193, Int.negSucc 263, Int.negSucc 332, Int.ofNat 132],
  [Int.negSucc 22, Int.negSucc 4, Int.ofNat 18, Int.ofNat 39, Int.negSucc 4, Int.negSucc 8, Int.ofNat 11, Int.ofNat 18, Int.negSucc 8, Int.negSucc 8, Int.ofNat 13, Int.negSucc 5, Int.ofNat 40, Int.ofNat 189, Int.negSucc 260, Int.negSucc 307, Int.ofNat 122],
  [Int.negSucc 3, Int.negSucc 10, Int.ofNat 14, Int.ofNat 22, Int.negSucc 9, Int.negSucc 3, Int.negSucc 56, Int.negSucc 5, Int.ofNat 0, Int.ofNat 3, Int.negSucc 9, Int.negSucc 6, Int.ofNat 21, Int.ofNat 151, Int.negSucc 210, Int.negSucc 253, Int.ofNat 97],
  [Int.negSucc 14, Int.negSucc 25, Int.negSucc 15, Int.negSucc 12, Int.ofNat 8, Int.ofNat 35, Int.negSucc 60, Int.negSucc 36, Int.negSucc 22, Int.ofNat 5, Int.ofNat 8, Int.negSucc 5, Int.ofNat 19, Int.ofNat 115, Int.negSucc 139, Int.negSucc 192, Int.ofNat 66],
  [Int.negSucc 9, Int.negSucc 24, Int.negSucc 14, Int.negSucc 12, Int.ofNat 11, Int.ofNat 29, Int.negSucc 29, Int.negSucc 50, Int.negSucc 14, Int.ofNat 12, Int.ofNat 7, Int.negSucc 11, Int.negSucc 2, Int.ofNat 65, Int.negSucc 87, Int.negSucc 122, Int.ofNat 34],
  [Int.negSucc 2, Int.negSucc 1, Int.negSucc 6, Int.negSucc 5, Int.ofNat 5, Int.ofNat 11, Int.negSucc 9, Int.negSucc 11, Int.negSucc 4, Int.ofNat 6, Int.ofNat 3, Int.negSucc 4, Int.ofNat 5, Int.ofNat 23, Int.negSucc 28, Int.negSucc 40, Int.ofNat 11]
]
private def V3_g5 : List (List Int) := [
  [Int.ofNat 28, Int.ofNat 23, Int.ofNat 17, Int.negSucc 11, Int.negSucc 38, Int.ofNat 116, Int.negSucc 0, Int.negSucc 30, Int.ofNat 20, Int.negSucc 111, Int.ofNat 17, Int.ofNat 17, Int.negSucc 11, Int.negSucc 82, Int.ofNat 252, Int.negSucc 303, Int.ofNat 59],
  [Int.ofNat 13, Int.negSucc 12, Int.negSucc 33, Int.ofNat 0, Int.negSucc 6, Int.negSucc 26, Int.negSucc 0, Int.negSucc 17, Int.negSucc 3, Int.negSucc 36, Int.negSucc 17, Int.ofNat 63, Int.negSucc 2, Int.negSucc 112, Int.ofNat 307, Int.negSucc 323, Int.ofNat 53],
  [Int.negSucc 26, Int.negSucc 2, Int.ofNat 8, Int.ofNat 4, Int.ofNat 34, Int.ofNat 1, Int.negSucc 42, Int.ofNat 8, Int.negSucc 1, Int.ofNat 15, Int.ofNat 17, Int.ofNat 95, Int.negSucc 0, Int.negSucc 117, Int.ofNat 292, Int.negSucc 314, Int.ofNat 46],
  [Int.negSucc 9, Int.negSucc 2, Int.ofNat 18, Int.negSucc 6, Int.ofNat 23, Int.negSucc 31, Int.negSucc 6, Int.ofNat 11, Int.negSucc 21, Int.ofNat 46, Int.ofNat 1, Int.ofNat 78, Int.negSucc 6, Int.negSucc 94, Int.ofNat 246, Int.negSucc 266, Int.ofNat 35],
  [Int.negSucc 8, Int.ofNat 3, Int.negSucc 11, Int.ofNat 17, Int.negSucc 2, Int.negSucc 43, Int.ofNat 47, Int.ofNat 11, Int.negSucc 10, Int.ofNat 48, Int.negSucc 0, Int.ofNat 63, Int.negSucc 5, Int.negSucc 62, Int.ofNat 191, Int.negSucc 194, Int.ofNat 26],
  [Int.ofNat 0, Int.negSucc 4, Int.negSucc 1, Int.ofNat 26, Int.negSucc 30, Int.negSucc 41, Int.ofNat 52, Int.ofNat 10, Int.negSucc 10, Int.ofNat 31, Int.negSucc 5, Int.ofNat 43, Int.negSucc 8, Int.negSucc 29, Int.ofNat 112, Int.negSucc 109, Int.ofNat 15],
  [Int.ofNat 16, Int.negSucc 5, Int.negSucc 5, Int.ofNat 3, Int.negSucc 8, Int.negSucc 14, Int.ofNat 12, Int.ofNat 3, Int.negSucc 0, Int.ofNat 16, Int.negSucc 2, Int.ofNat 15, Int.negSucc 3, Int.negSucc 10, Int.ofNat 34, Int.negSucc 33, Int.ofNat 5]
]
private def V3_g6 : List (List Int) := [
  [Int.negSucc 11, Int.ofNat 3, Int.ofNat 12, Int.negSucc 15, Int.negSucc 9, Int.ofNat 39, Int.ofNat 18, Int.ofNat 50, Int.negSucc 28, Int.ofNat 232, Int.negSucc 12, Int.negSucc 155, Int.ofNat 9, Int.negSucc 28, Int.ofNat 76, Int.negSucc 72, Int.ofNat 16],
  [Int.ofNat 22, Int.ofNat 10, Int.negSucc 12, Int.ofNat 3, Int.negSucc 11, Int.ofNat 10, Int.ofNat 9, Int.ofNat 10, Int.negSucc 6, Int.ofNat 121, Int.negSucc 18, Int.negSucc 246, Int.ofNat 16, Int.negSucc 34, Int.ofNat 88, Int.negSucc 80, Int.ofNat 11],
  [Int.ofNat 7, Int.negSucc 5, Int.negSucc 12, Int.ofNat 8, Int.ofNat 7, Int.negSucc 6, Int.negSucc 24, Int.ofNat 1, Int.ofNat 2, Int.ofNat 2, Int.ofNat 5, Int.negSucc 327, Int.ofNat 20, Int.negSucc 28, Int.ofNat 74, Int.negSucc 70, Int.ofNat 10],
  [Int.negSucc 33, Int.ofNat 0, Int.ofNat 13, Int.negSucc 0, Int.ofNat 9, Int.negSucc 16, Int.negSucc 1, Int.negSucc 13, Int.ofNat 8, Int.negSucc 81, Int.ofNat 12, Int.negSucc 266, Int.ofNat 15, Int.negSucc 26, Int.ofNat 71, Int.negSucc 69, Int.ofNat 8],
  [Int.negSucc 9, Int.negSucc 4, Int.ofNat 2, Int.ofNat 3, Int.ofNat 6, Int.negSucc 29, Int.ofNat 20, Int.negSucc 16, Int.ofNat 7, Int.negSucc 124, Int.ofNat 14, Int.negSucc 208, Int.ofNat 15, Int.negSucc 16, Int.ofNat 55, Int.negSucc 52, Int.ofNat 6],
  [Int.ofNat 17, Int.ofNat 0, Int.ofNat 1, Int.negSucc 0, Int.ofNat 0, Int.negSucc 23, Int.ofNat 14, Int.negSucc 10, Int.ofNat 12, Int.negSucc 98, Int.ofNat 9, Int.negSucc 128, Int.ofNat 15, Int.negSucc 9, Int.ofNat 31, Int.negSucc 28, Int.ofNat 3],
  [Int.ofNat 18, Int.negSucc 1, Int.ofNat 3, Int.negSucc 1, Int.ofNat 0, Int.negSucc 9, Int.ofNat 6, Int.negSucc 0, Int.ofNat 7, Int.negSucc 32, Int.ofNat 3, Int.negSucc 44, Int.ofNat 7, Int.negSucc 2, Int.ofNat 9, Int.negSucc 8, Int.ofNat 0]
]
private def V3 : List (List Int) := V3_g0 ++ V3_g1 ++ V3_g2 ++ V3_g3 ++ V3_g4 ++ V3_g5 ++ V3_g6

private def V4top_g0 : List (List Int) := [
  [Int.ofNat 23, Int.ofNat 8, Int.ofNat 4, Int.negSucc 14, Int.ofNat 13, Int.ofNat 7, Int.negSucc 54, Int.negSucc 20, Int.negSucc 31, Int.ofNat 57, Int.negSucc 4, Int.negSucc 99, Int.ofNat 63, Int.ofNat 13, Int.negSucc 63, Int.negSucc 47, Int.negSucc 18, Int.negSucc 37, Int.negSucc 86, Int.negSucc 99, Int.ofNat 9, Int.negSucc 19, Int.negSucc 157, Int.negSucc 22, Int.negSucc 3, Int.negSucc 8, Int.ofNat 208, Int.negSucc 150, Int.ofNat 61, Int.ofNat 306, Int.negSucc 64, Int.ofNat 6, Int.ofNat 115, Int.negSucc 208],
  [Int.negSucc 11, Int.negSucc 16, Int.ofNat 1, Int.ofNat 9, Int.negSucc 20, Int.negSucc 35, Int.ofNat 29, Int.ofNat 55, Int.ofNat 57, Int.ofNat 31, Int.ofNat 15, Int.ofNat 4, Int.ofNat 52, Int.ofNat 127, Int.negSucc 61, Int.ofNat 115, Int.negSucc 75, Int.negSucc 47, Int.ofNat 15, Int.negSucc 1, Int.negSucc 13, Int.negSucc 4, Int.negSucc 171, Int.ofNat 121, Int.ofNat 9, Int.ofNat 4, Int.ofNat 219, Int.negSucc 110, Int.negSucc 79, Int.ofNat 336, Int.negSucc 155, Int.negSucc 20, Int.ofNat 134, Int.negSucc 111],
  [Int.ofNat 29, Int.negSucc 10, Int.ofNat 25, Int.negSucc 19, Int.ofNat 19, Int.ofNat 24, Int.negSucc 16, Int.ofNat 2, Int.ofNat 0, Int.ofNat 2, Int.ofNat 101, Int.ofNat 39, Int.ofNat 0, Int.ofNat 4, Int.negSucc 26, Int.ofNat 6, Int.negSucc 112, Int.negSucc 66, Int.ofNat 99, Int.ofNat 86, Int.negSucc 24, Int.ofNat 0, Int.negSucc 140, Int.ofNat 9, Int.ofNat 4, Int.negSucc 14, Int.ofNat 139, Int.negSucc 35, Int.negSucc 129, Int.ofNat 282, Int.negSucc 214, Int.negSucc 59, Int.ofNat 176, Int.negSucc 18],
  [Int.negSucc 5, Int.negSucc 8, Int.negSucc 20, Int.ofNat 29, Int.negSucc 22, Int.ofNat 19, Int.ofNat 12, Int.ofNat 14, Int.negSucc 5, Int.negSucc 18, Int.negSucc 5, Int.negSucc 1, Int.negSucc 4, Int.negSucc 61, Int.ofNat 26, Int.negSucc 13, Int.negSucc 21, Int.negSucc 21, Int.ofNat 60, Int.ofNat 193, Int.negSucc 54, Int.ofNat 41, Int.negSucc 100, Int.ofNat 39, Int.ofNat 7, Int.negSucc 16, Int.ofNat 106, Int.negSucc 58, Int.ofNat 59, Int.ofNat 195, Int.negSucc 136, Int.negSucc 74, Int.ofNat 213, Int.ofNat 50],
  [Int.ofNat 4, Int.negSucc 3, Int.negSucc 22, Int.ofNat 11, Int.ofNat 8, Int.negSucc 7, Int.negSucc 26, Int.ofNat 1, Int.ofNat 6, Int.negSucc 12, Int.negSucc 98, Int.negSucc 16, Int.ofNat 1, Int.negSucc 63, Int.ofNat 23, Int.negSucc 22, Int.ofNat 45, Int.negSucc 6, Int.ofNat 41, Int.ofNat 212, Int.ofNat 27, Int.ofNat 1, Int.negSucc 89, Int.ofNat 20, Int.negSucc 0, Int.negSucc 4, Int.ofNat 99, Int.negSucc 58, Int.ofNat 1, Int.ofNat 199, Int.ofNat 21, Int.ofNat 36, Int.ofNat 194, Int.ofNat 67],
  [Int.negSucc 9, Int.ofNat 11, Int.ofNat 36, Int.negSucc 12, Int.ofNat 19, Int.negSucc 20, Int.ofNat 5, Int.negSucc 13, Int.ofNat 17, Int.negSucc 11, Int.negSucc 119, Int.negSucc 19, Int.negSucc 8, Int.negSucc 57, Int.ofNat 8, Int.negSucc 33, Int.ofNat 54, Int.negSucc 17, Int.ofNat 25, Int.ofNat 160, Int.ofNat 20, Int.negSucc 52, Int.negSucc 68, Int.ofNat 19, Int.negSucc 11, Int.negSucc 6, Int.ofNat 81, Int.negSucc 63, Int.ofNat 28, Int.ofNat 105, Int.negSucc 55, Int.ofNat 128, Int.ofNat 115, Int.ofNat 45],
  [Int.negSucc 3, Int.ofNat 9, Int.ofNat 18, Int.negSucc 38, Int.negSucc 25, Int.ofNat 7, Int.ofNat 22, Int.ofNat 0, Int.ofNat 14, Int.ofNat 6, Int.negSucc 39, Int.negSucc 15, Int.ofNat 4, Int.negSucc 16, Int.ofNat 2, Int.negSucc 13, Int.ofNat 26, Int.negSucc 10, Int.ofNat 4, Int.ofNat 62, Int.ofNat 14, Int.negSucc 37, Int.negSucc 27, Int.ofNat 1, Int.ofNat 105, Int.negSucc 6, Int.ofNat 18, Int.negSucc 25, Int.ofNat 13, Int.ofNat 30, Int.negSucc 22, Int.ofNat 49, Int.ofNat 37, Int.ofNat 15]
]
private def V4top_g1 : List (List Int) := [
  [Int.ofNat 36, Int.ofNat 9, Int.ofNat 24, Int.negSucc 1, Int.negSucc 22, Int.ofNat 15, Int.ofNat 12, Int.ofNat 24, Int.ofNat 50, Int.negSucc 39, Int.negSucc 34, Int.ofNat 90, Int.negSucc 71, Int.ofNat 88, Int.ofNat 223, Int.negSucc 26, Int.ofNat 78, Int.ofNat 96, Int.ofNat 77, Int.negSucc 74, Int.ofNat 11, Int.negSucc 15, Int.ofNat 92, Int.negSucc 40, Int.negSucc 3, Int.negSucc 7, Int.ofNat 58, Int.negSucc 86, Int.ofNat 65, Int.ofNat 194, Int.negSucc 18, Int.ofNat 5, Int.ofNat 11, Int.negSucc 50],
  [Int.negSucc 11, Int.ofNat 11, Int.negSucc 3, Int.negSucc 28, Int.ofNat 58, Int.ofNat 11, Int.negSucc 35, Int.negSucc 16, Int.negSucc 31, Int.ofNat 30, Int.negSucc 37, Int.ofNat 57, Int.negSucc 66, Int.negSucc 36, Int.ofNat 142, Int.ofNat 1, Int.ofNat 99, Int.ofNat 136, Int.ofNat 68, Int.negSucc 107, Int.ofNat 10, Int.negSucc 1, Int.ofNat 59, Int.ofNat 54, Int.ofNat 5, Int.negSucc 15, Int.ofNat 63, Int.negSucc 65, Int.negSucc 9, Int.ofNat 183, Int.negSucc 60, Int.negSucc 4, Int.ofNat 14, Int.negSucc 8],
  [Int.negSucc 15, Int.negSucc 13, Int.negSucc 2, Int.ofNat 21, Int.negSucc 25, Int.negSucc 40, Int.ofNat 24, Int.negSucc 0, Int.negSucc 23, Int.ofNat 72, Int.negSucc 7, Int.ofNat 13, Int.negSucc 16, Int.negSucc 70, Int.ofNat 66, Int.negSucc 22, Int.ofNat 117, Int.ofNat 154, Int.ofNat 74, Int.negSucc 164, Int.ofNat 5, Int.negSucc 20, Int.ofNat 49, Int.negSucc 40, Int.negSucc 3, Int.negSucc 10, Int.ofNat 36, Int.negSucc 55, Int.negSucc 37, Int.ofNat 133, Int.negSucc 75, Int.negSucc 20, Int.ofNat 36, Int.ofNat 18],
  [Int.negSucc 1, Int.negSucc 14, Int.ofNat 8, Int.ofNat 5, Int.ofNat 1, Int.negSucc 7, Int.negSucc 16, Int.ofNat 22, Int.ofNat 14, Int.ofNat 18, Int.ofNat 17, Int.negSucc 51, Int.ofNat 19, Int.negSucc 19, Int.negSucc 45, Int.negSucc 3, Int.ofNat 128, Int.ofNat 153, Int.ofNat 30, Int.negSucc 192, Int.negSucc 0, Int.negSucc 2, Int.ofNat 37, Int.negSucc 18, Int.negSucc 3, Int.negSucc 5, Int.ofNat 37, Int.negSucc 38, Int.ofNat 35, Int.ofNat 88, Int.negSucc 47, Int.negSucc 28, Int.ofNat 57, Int.ofNat 37],
  [Int.negSucc 10, Int.ofNat 10, Int.negSucc 4, Int.negSucc 14, Int.negSucc 8, Int.ofNat 4, Int.ofNat 5, Int.ofNat 5, Int.ofNat 19, Int.negSucc 65, Int.ofNat 50, Int.negSucc 63, Int.ofNat 32, Int.ofNat 26, Int.negSucc 85, Int.negSucc 9, Int.ofNat 102, Int.ofNat 121, Int.ofNat 21, Int.negSucc 180, Int.ofNat 30, Int.negSucc 2, Int.ofNat 33, Int.negSucc 13, Int.negSucc 1, Int.negSucc 2, Int.ofNat 15, Int.negSucc 21, Int.ofNat 10, Int.ofNat 81, Int.ofNat 14, Int.ofNat 15, Int.ofNat 56, Int.ofNat 38],
  [Int.ofNat 12, Int.ofNat 15, Int.negSucc 16, Int.ofNat 29, Int.negSucc 2, Int.ofNat 19, Int.ofNat 9, Int.negSucc 3, Int.ofNat 24, Int.negSucc 65, Int.ofNat 63, Int.negSucc 50, Int.ofNat 57, Int.ofNat 63, Int.negSucc 74, Int.ofNat 15, Int.ofNat 73, Int.ofNat 79, Int.ofNat 21, Int.negSucc 128, Int.ofNat 15, Int.negSucc 45, Int.ofNat 27, Int.negSucc 10, Int.negSucc 7, Int.ofNat 7, Int.ofNat 5, Int.negSucc 17, Int.ofNat 22, Int.ofNat 37, Int.negSucc 12, Int.ofNat 47, Int.ofNat 33, Int.ofNat 23],
  [Int.ofNat 9, Int.ofNat 2, Int.negSucc 12, Int.ofNat 38, Int.ofNat 19, Int.ofNat 8, Int.ofNat 3, Int.negSucc 3, Int.ofNat 1, Int.negSucc 34, Int.ofNat 24, Int.negSucc 18, Int.ofNat 17, Int.ofNat 23, Int.negSucc 20, Int.ofNat 13, Int.ofNat 31, Int.ofNat 26, Int.ofNat 3, Int.negSucc 43, Int.ofNat 7, Int.negSucc 17, Int.ofNat 5, Int.negSucc 6, Int.ofNat 41, Int.negSucc 0, Int.negSucc 2, Int.negSucc 3, Int.ofNat 9, Int.ofNat 10, Int.negSucc 5, Int.ofNat 18, Int.ofNat 11, Int.ofNat 8]
]
private def V4top_g2 : List (List Int) := [
  [Int.ofNat 13, Int.ofNat 19, Int.ofNat 6, Int.negSucc 12, Int.ofNat 9, Int.ofNat 28, Int.ofNat 3, Int.ofNat 32, Int.negSucc 6, Int.negSucc 26, Int.ofNat 8, Int.ofNat 100, Int.negSucc 44, Int.negSucc 97, Int.negSucc 218, Int.negSucc 32, Int.ofNat 17, Int.ofNat 18, Int.ofNat 37, Int.ofNat 64, Int.negSucc 12, Int.ofNat 30, Int.ofNat 300, Int.negSucc 63, Int.negSucc 5, Int.negSucc 19, Int.negSucc 135, Int.negSucc 36, Int.ofNat 97, Int.ofNat 175, Int.negSucc 6, Int.ofNat 8, Int.negSucc 31, Int.negSucc 5],
  [Int.negSucc 26, Int.negSucc 21, Int.negSucc 3, Int.negSucc 8, Int.negSucc 16, Int.negSucc 27, Int.ofNat 30, Int.negSucc 15, Int.ofNat 13, Int.negSucc 30, Int.negSucc 12, Int.negSucc 25, Int.ofNat 13, Int.negSucc 64, Int.negSucc 92, Int.ofNat 24, Int.negSucc 11, Int.negSucc 23, Int.negSucc 18, Int.ofNat 95, Int.negSucc 8, Int.ofNat 37, Int.ofNat 384, Int.negSucc 28, Int.negSucc 0, Int.negSucc 8, Int.negSucc 95, Int.negSucc 49, Int.ofNat 47, Int.ofNat 188, Int.negSucc 40, Int.negSucc 1, Int.negSucc 22, Int.ofNat 24],
  [Int.ofNat 0, Int.ofNat 20, Int.negSucc 7, Int.ofNat 18, Int.ofNat 14, Int.ofNat 9, Int.negSucc 21, Int.negSucc 6, Int.ofNat 4, Int.ofNat 48, Int.negSucc 6, Int.negSucc 80, Int.ofNat 42, Int.negSucc 3, Int.negSucc 4, Int.negSucc 19, Int.negSucc 22, Int.negSucc 54, Int.negSucc 72, Int.ofNat 63, Int.negSucc 7, Int.ofNat 29, Int.ofNat 319, Int.negSucc 86, Int.negSucc 5, Int.negSucc 5, Int.negSucc 37, Int.negSucc 59, Int.ofNat 13, Int.ofNat 177, Int.negSucc 59, Int.negSucc 10, Int.negSucc 1, Int.ofNat 49],
  [Int.ofNat 18, Int.ofNat 9, Int.ofNat 8, Int.negSucc 1, Int.negSucc 1, Int.negSucc 22, Int.negSucc 22, Int.ofNat 4, Int.ofNat 42, Int.ofNat 25, Int.negSucc 4, Int.negSucc 17, Int.ofNat 39, Int.ofNat 83, Int.ofNat 59, Int.ofNat 10, Int.negSucc 49, Int.negSucc 69, Int.negSucc 91, Int.ofNat 39, Int.negSucc 2, Int.ofNat 26, Int.ofNat 246, Int.negSucc 53, Int.negSucc 2, Int.negSucc 5, Int.negSucc 31, Int.negSucc 48, Int.ofNat 52, Int.ofNat 129, Int.negSucc 39, Int.negSucc 17, Int.ofNat 18, Int.ofNat 56],
  [Int.negSucc 12, Int.ofNat 6, Int.ofNat 32, Int.negSucc 7, Int.ofNat 5, Int.ofNat 2, Int.negSucc 20, Int.ofNat 5, Int.ofNat 6, Int.ofNat 5, Int.ofNat 48, Int.ofNat 33, Int.ofNat 17, Int.ofNat 122, Int.ofNat 85, Int.ofNat 16, Int.negSucc 54, Int.negSucc 67, Int.negSucc 60, Int.ofNat 54, Int.ofNat 0, Int.ofNat 30, Int.ofNat 192, Int.negSucc 36, Int.negSucc 1, Int.negSucc 9, Int.negSucc 46, Int.negSucc 17, Int.ofNat 27, Int.ofNat 86, Int.ofNat 8, Int.ofNat 12, Int.ofNat 21, Int.ofNat 41],
  [Int.ofNat 2, Int.negSucc 11, Int.negSucc 41, Int.negSucc 2, Int.ofNat 10, Int.ofNat 20, Int.negSucc 36, Int.ofNat 4, Int.negSucc 46, Int.negSucc 26, Int.ofNat 56, Int.ofNat 49, Int.negSucc 6, Int.ofNat 88, Int.ofNat 87, Int.ofNat 14, Int.negSucc 42, Int.negSucc 46, Int.negSucc 41, Int.ofNat 34, Int.negSucc 3, Int.ofNat 2, Int.ofNat 147, Int.negSucc 24, Int.negSucc 3, Int.negSucc 1, Int.negSucc 52, Int.negSucc 5, Int.ofNat 33, Int.ofNat 51, Int.negSucc 9, Int.ofNat 32, Int.ofNat 13, Int.ofNat 25],
  [Int.negSucc 3, Int.negSucc 2, Int.negSucc 21, Int.negSucc 1, Int.negSucc 1, Int.negSucc 5, Int.negSucc 21, Int.ofNat 2, Int.negSucc 16, Int.negSucc 17, Int.ofNat 16, Int.ofNat 14, Int.negSucc 3, Int.ofNat 26, Int.ofNat 32, Int.ofNat 10, Int.negSucc 23, Int.negSucc 34, Int.negSucc 12, Int.ofNat 12, Int.negSucc 1, Int.ofNat 1, Int.ofNat 63, Int.negSucc 13, Int.ofNat 25, Int.negSucc 3, Int.negSucc 25, Int.ofNat 3, Int.ofNat 15, Int.ofNat 12, Int.negSucc 2, Int.ofNat 13, Int.ofNat 5, Int.ofNat 8]
]
private def V4top_g3 : List (List Int) := [
  [Int.ofNat 5, Int.ofNat 25, Int.ofNat 17, Int.negSucc 3, Int.negSucc 18, Int.negSucc 42, Int.negSucc 4, Int.negSucc 5, Int.negSucc 83, Int.negSucc 3, Int.ofNat 59, Int.negSucc 169, Int.ofNat 78, Int.negSucc 13, Int.ofNat 139, Int.negSucc 14, Int.negSucc 1, Int.negSucc 8, Int.ofNat 1, Int.ofNat 46, Int.ofNat 0, Int.negSucc 0, Int.negSucc 58, Int.ofNat 10, Int.ofNat 2, Int.negSucc 46, Int.negSucc 444, Int.ofNat 173, Int.ofNat 131, Int.ofNat 62, Int.ofNat 32, Int.ofNat 10, Int.negSucc 68, Int.ofNat 24],
  [Int.negSucc 28, Int.negSucc 18, Int.negSucc 7, Int.negSucc 9, Int.negSucc 7, Int.ofNat 1, Int.negSucc 24, Int.ofNat 25, Int.ofNat 32, Int.negSucc 73, Int.negSucc 13, Int.negSucc 33, Int.ofNat 19, Int.negSucc 23, Int.ofNat 46, Int.ofNat 24, Int.ofNat 1, Int.ofNat 0, Int.ofNat 6, Int.ofNat 22, Int.ofNat 8, Int.negSucc 8, Int.negSucc 134, Int.ofNat 90, Int.ofNat 8, Int.negSucc 57, Int.negSucc 509, Int.ofNat 160, Int.ofNat 100, Int.ofNat 105, Int.ofNat 1, Int.ofNat 4, Int.negSucc 55, Int.ofNat 52],
  [Int.ofNat 24, Int.negSucc 14, Int.ofNat 11, Int.ofNat 1, Int.ofNat 13, Int.ofNat 49, Int.ofNat 14, Int.negSucc 3, Int.ofNat 40, Int.negSucc 34, Int.negSucc 25, Int.ofNat 34, Int.negSucc 13, Int.ofNat 27, Int.negSucc 18, Int.negSucc 18, Int.ofNat 1, Int.negSucc 11, Int.negSucc 17, Int.negSucc 13, Int.ofNat 16, Int.negSucc 15, Int.negSucc 168, Int.ofNat 45, Int.ofNat 2, Int.negSucc 51, Int.negSucc 473, Int.ofNat 113, Int.ofNat 80, Int.ofNat 127, Int.negSucc 21, Int.negSucc 3, Int.negSucc 35, Int.ofNat 68],
  [Int.negSucc 12, Int.ofNat 10, Int.negSucc 19, Int.ofNat 12, Int.ofNat 30, Int.ofNat 15, Int.ofNat 27, Int.negSucc 12, Int.ofNat 32, Int.ofNat 28, Int.negSucc 17, Int.ofNat 68, Int.negSucc 32, Int.ofNat 25, Int.negSucc 51, Int.ofNat 14, Int.negSucc 13, Int.negSucc 4, Int.negSucc 6, Int.negSucc 43, Int.ofNat 15, Int.negSucc 9, Int.negSucc 142, Int.ofNat 42, Int.ofNat 1, Int.negSucc 44, Int.negSucc 373, Int.ofNat 78, Int.ofNat 95, Int.ofNat 102, Int.negSucc 10, Int.negSucc 6, Int.negSucc 16, Int.ofNat 64],
  [Int.ofNat 1, Int.ofNat 23, Int.negSucc 5, Int.negSucc 8, Int.ofNat 8, Int.negSucc 26, Int.negSucc 27, Int.ofNat 7, Int.negSucc 17, Int.ofNat 72, Int.ofNat 15, Int.ofNat 79, Int.negSucc 45, Int.negSucc 19, Int.negSucc 71, Int.ofNat 8, Int.negSucc 30, Int.negSucc 8, Int.ofNat 5, Int.negSucc 57, Int.negSucc 3, Int.negSucc 11, Int.negSucc 105, Int.ofNat 31, Int.ofNat 2, Int.negSucc 35, Int.negSucc 248, Int.ofNat 61, Int.ofNat 56, Int.ofNat 73, Int.ofNat 15, Int.ofNat 10, Int.negSucc 4, Int.ofNat 50],
  [Int.ofNat 17, Int.ofNat 7, Int.ofNat 15, Int.negSucc 2, Int.negSucc 35, Int.negSucc 42, Int.negSucc 23, Int.ofNat 16, Int.negSucc 28, Int.ofNat 71, Int.ofNat 9, Int.ofNat 58, Int.negSucc 33, Int.negSucc 47, Int.negSucc 67, Int.ofNat 10, Int.negSucc 32, Int.negSucc 7, Int.negSucc 0, Int.negSucc 39, Int.ofNat 4, Int.ofNat 2, Int.negSucc 67, Int.ofNat 19, Int.ofNat 2, Int.negSucc 22, Int.negSucc 162, Int.ofNat 53, Int.ofNat 41, Int.ofNat 26, Int.negSucc 0, Int.ofNat 23, Int.negSucc 1, Int.ofNat 28],
  [Int.ofNat 3, Int.ofNat 3, Int.ofNat 6, Int.ofNat 2, Int.negSucc 15, Int.negSucc 26, Int.negSucc 25, Int.ofNat 3, Int.negSucc 11, Int.ofNat 31, Int.ofNat 2, Int.ofNat 19, Int.negSucc 5, Int.negSucc 23, Int.negSucc 33, Int.ofNat 1, Int.negSucc 13, Int.negSucc 0, Int.ofNat 2, Int.negSucc 12, Int.ofNat 1, Int.negSucc 2, Int.negSucc 25, Int.ofNat 6, Int.ofNat 13, Int.negSucc 6, Int.negSucc 48, Int.ofNat 20, Int.ofNat 15, Int.ofNat 8, Int.negSucc 0, Int.ofNat 8, Int.negSucc 0, Int.ofNat 9]
]
private def V4top_g4 : List (List Int) := [
  [Int.ofNat 5, Int.ofNat 10, Int.ofNat 20, Int.ofNat 36, Int.negSucc 68, Int.ofNat 15, Int.negSucc 95, Int.negSucc 75, Int.ofNat 68, Int.negSucc 10, Int.ofNat 2, Int.ofNat 75, Int.ofNat 62, Int.negSucc 14, Int.negSucc 21, Int.ofNat 7, Int.ofNat 14, Int.ofNat 22, Int.ofNat 24, Int.ofNat 2, Int.negSucc 1, Int.ofNat 1, Int.negSucc 2, Int.negSucc 10, Int.negSucc 1, Int.ofNat 13, Int.ofNat 145, Int.ofNat 473, Int.ofNat 75, Int.negSucc 195, Int.ofNat 79, Int.ofNat 9, Int.negSucc 97, Int.ofNat 51],
  [Int.negSucc 20, Int.negSucc 1, Int.negSucc 16, Int.negSucc 20, Int.ofNat 27, Int.negSucc 3, Int.negSucc 18, Int.ofNat 105, Int.negSucc 19, Int.negSucc 29, Int.negSucc 6, Int.ofNat 2, Int.negSucc 15, Int.negSucc 0, Int.ofNat 0, Int.negSucc 14, Int.ofNat 11, Int.ofNat 1, Int.negSucc 8, Int.ofNat 15, Int.ofNat 1, Int.ofNat 2, Int.ofNat 12, Int.ofNat 28, Int.ofNat 4, Int.ofNat 35, Int.ofNat 230, Int.ofNat 550, Int.ofNat 59, Int.negSucc 173, Int.ofNat 53, Int.ofNat 5, Int.negSucc 85, Int.ofNat 70],
  [Int.ofNat 20, Int.ofNat 7, Int.ofNat 3, Int.ofNat 5, Int.negSucc 9, Int.negSucc 26, Int.ofNat 18, Int.negSucc 16, Int.negSucc 71, Int.negSucc 9, Int.negSucc 32, Int.ofNat 29, Int.negSucc 20, Int.ofNat 25, Int.negSucc 34, Int.negSucc 16, Int.ofNat 5, Int.negSucc 17, Int.negSucc 40, Int.ofNat 0, Int.ofNat 16, Int.negSucc 7, Int.ofNat 10, Int.negSucc 0, Int.ofNat 1, Int.ofNat 50, Int.ofNat 228, Int.ofNat 524, Int.ofNat 54, Int.negSucc 139, Int.ofNat 36, Int.ofNat 3, Int.negSucc 70, Int.ofNat 78],
  [Int.negSucc 18, Int.negSucc 12, Int.negSucc 3, Int.ofNat 3, Int.ofNat 14, Int.ofNat 3, Int.ofNat 54, Int.negSucc 20, Int.negSucc 7, Int.ofNat 15, Int.negSucc 0, Int.negSucc 20, Int.negSucc 4, Int.negSucc 11, Int.ofNat 11, Int.ofNat 17, Int.negSucc 15, Int.negSucc 12, Int.negSucc 12, Int.negSucc 11, Int.ofNat 14, Int.negSucc 5, Int.ofNat 11, Int.negSucc 10, Int.ofNat 0, Int.ofNat 29, Int.ofNat 191, Int.ofNat 418, Int.ofNat 63, Int.negSucc 105, Int.ofNat 37, Int.ofNat 5, Int.negSucc 51, Int.ofNat 72],
  [Int.ofNat 4, Int.negSucc 5, Int.ofNat 3, Int.negSucc 25, Int.ofNat 34, Int.ofNat 10, Int.ofNat 22, Int.ofNat 7, Int.ofNat 59, Int.ofNat 29, Int.ofNat 37, Int.negSucc 60, Int.negSucc 7, Int.negSucc 31, Int.ofNat 35, Int.negSucc 1, Int.negSucc 30, Int.negSucc 17, Int.ofNat 3, Int.negSucc 0, Int.negSucc 4, Int.ofNat 8, Int.negSucc 3, Int.ofNat 1, Int.ofNat 1, Int.ofNat 11, Int.ofNat 149, Int.ofNat 297, Int.ofNat 40, Int.negSucc 74, Int.ofNat 34, Int.ofNat 12, Int.negSucc 35, Int.ofNat 51],
  [Int.ofNat 17, Int.ofNat 14, Int.ofNat 1, Int.negSucc 24, Int.ofNat 29, Int.ofNat 30, Int.ofNat 25, Int.ofNat 6, Int.ofNat 53, Int.ofNat 15, Int.ofNat 15, Int.negSucc 68, Int.ofNat 3, Int.negSucc 18, Int.ofNat 34, Int.ofNat 8, Int.negSucc 23, Int.negSucc 14, Int.negSucc 11, Int.ofNat 0, Int.negSucc 15, Int.ofNat 11, Int.negSucc 11, Int.ofNat 1, Int.ofNat 3, Int.ofNat 11, Int.ofNat 94, Int.ofNat 189, Int.ofNat 23, Int.negSucc 50, Int.ofNat 18, Int.ofNat 11, Int.negSucc 19, Int.ofNat 29],
  [Int.ofNat 4, Int.ofNat 12, Int.ofNat 3, Int.negSucc 6, Int.ofNat 11, Int.ofNat 9, Int.ofNat 5, Int.negSucc 0, Int.ofNat 21, Int.ofNat 4, Int.ofNat 10, Int.negSucc 22, Int.negSucc 0, Int.negSucc 6, Int.ofNat 11, Int.ofNat 1, Int.negSucc 3, Int.negSucc 6, Int.negSucc 5, Int.ofNat 3, Int.negSucc 0, Int.negSucc 2, Int.ofNat 2, Int.ofNat 0, Int.ofNat 1, Int.ofNat 2, Int.ofNat 29, Int.ofNat 57, Int.ofNat 7, Int.negSucc 15, Int.ofNat 6, Int.ofNat 1, Int.negSucc 6, Int.ofNat 9]
]
private def V4top_g5 : List (List Int) := [
  [Int.negSucc 7, Int.ofNat 52, Int.negSucc 1, Int.ofNat 19, Int.negSucc 9, Int.ofNat 10, Int.negSucc 25, Int.negSucc 6, Int.ofNat 45, Int.ofNat 42, Int.ofNat 20, Int.negSucc 101, Int.negSucc 203, Int.ofNat 61, Int.negSucc 30, Int.negSucc 9, Int.negSucc 27, Int.negSucc 20, Int.ofNat 13, Int.ofNat 20, Int.negSucc 7, Int.ofNat 3, Int.negSucc 19, Int.negSucc 15, Int.negSucc 8, Int.negSucc 233, Int.ofNat 24, Int.negSucc 173, Int.negSucc 135, Int.negSucc 403, Int.ofNat 115, Int.ofNat 11, Int.negSucc 111, Int.ofNat 65],
  [Int.negSucc 29, Int.negSucc 57, Int.ofNat 7, Int.negSucc 18, Int.ofNat 9, Int.negSucc 18, Int.negSucc 34, Int.ofNat 32, Int.ofNat 1, Int.ofNat 1, Int.ofNat 3, Int.negSucc 8, Int.negSucc 11, Int.ofNat 16, Int.negSucc 15, Int.negSucc 31, Int.ofNat 1, Int.negSucc 16, Int.negSucc 30, Int.negSucc 1, Int.ofNat 2, Int.ofNat 2, Int.negSucc 16, Int.ofNat 23, Int.negSucc 4, Int.negSucc 340, Int.ofNat 24, Int.negSucc 207, Int.negSucc 169, Int.negSucc 392, Int.ofNat 96, Int.ofNat 8, Int.negSucc 100, Int.ofNat 77],
  [Int.ofNat 53, Int.negSucc 13, Int.ofNat 9, Int.ofNat 1, Int.ofNat 6, Int.negSucc 2, Int.ofNat 43, Int.ofNat 0, Int.negSucc 15, Int.negSucc 23, Int.ofNat 2, Int.negSucc 11, Int.ofNat 2, Int.negSucc 22, Int.negSucc 2, Int.ofNat 18, Int.ofNat 0, Int.negSucc 12, Int.negSucc 22, Int.ofNat 5, Int.ofNat 8, Int.negSucc 6, Int.negSucc 9, Int.ofNat 3, Int.negSucc 6, Int.negSucc 381, Int.ofNat 33, Int.negSucc 192, Int.negSucc 161, Int.negSucc 362, Int.ofNat 79, Int.ofNat 8, Int.negSucc 86, Int.ofNat 87],
  [Int.negSucc 0, Int.ofNat 5, Int.negSucc 8, Int.ofNat 4, Int.negSucc 15, Int.ofNat 5, Int.ofNat 11, Int.negSucc 29, Int.ofNat 3, Int.negSucc 24, Int.negSucc 14, Int.ofNat 28, Int.ofNat 73, Int.negSucc 28, Int.ofNat 21, Int.ofNat 7, Int.negSucc 10, Int.negSucc 6, Int.ofNat 6, Int.negSucc 0, Int.ofNat 2, Int.negSucc 8, Int.negSucc 1, Int.negSucc 6, Int.negSucc 7, Int.negSucc 326, Int.ofNat 31, Int.negSucc 159, Int.negSucc 118, Int.negSucc 294, Int.ofNat 73, Int.ofNat 10, Int.negSucc 67, Int.ofNat 72],
  [Int.negSucc 26, Int.ofNat 25, Int.negSucc 12, Int.negSucc 13, Int.ofNat 4, Int.ofNat 16, Int.negSucc 23, Int.ofNat 12, Int.negSucc 9, Int.negSucc 19, Int.negSucc 22, Int.ofNat 64, Int.ofNat 103, Int.negSucc 19, Int.ofNat 19, Int.ofNat 8, Int.ofNat 3, Int.ofNat 7, Int.negSucc 2, Int.ofNat 3, Int.ofNat 0, Int.ofNat 4, Int.negSucc 12, Int.negSucc 0, Int.negSucc 4, Int.negSucc 240, Int.ofNat 35, Int.negSucc 127, Int.negSucc 88, Int.negSucc 206, Int.ofNat 51, Int.ofNat 10, Int.negSucc 47, Int.ofNat 48],
  [Int.negSucc 2, Int.ofNat 23, Int.ofNat 9, Int.ofNat 2, Int.ofNat 0, Int.ofNat 4, Int.negSucc 5, Int.ofNat 24, Int.negSucc 41, Int.negSucc 9, Int.negSucc 11, Int.ofNat 62, Int.ofNat 98, Int.negSucc 6, Int.ofNat 14, Int.ofNat 7, Int.ofNat 0, Int.ofNat 8, Int.ofNat 2, Int.negSucc 4, Int.ofNat 11, Int.negSucc 4, Int.negSucc 16, Int.ofNat 0, Int.negSucc 2, Int.negSucc 128, Int.ofNat 28, Int.negSucc 72, Int.negSucc 49, Int.negSucc 116, Int.ofNat 28, Int.ofNat 5, Int.negSucc 26, Int.ofNat 26],
  [Int.ofNat 13, Int.ofNat 1, Int.ofNat 3, Int.ofNat 15, Int.ofNat 0, Int.ofNat 5, Int.ofNat 4, Int.ofNat 5, Int.negSucc 13, Int.ofNat 0, Int.negSucc 7, Int.ofNat 26, Int.ofNat 36, Int.negSucc 3, Int.ofNat 3, Int.ofNat 5, Int.ofNat 3, Int.ofNat 0, Int.ofNat 2, Int.negSucc 3, Int.ofNat 0, Int.negSucc 1, Int.negSucc 2, Int.negSucc 0, Int.negSucc 3, Int.negSucc 37, Int.ofNat 8, Int.negSucc 21, Int.negSucc 16, Int.negSucc 36, Int.ofNat 9, Int.ofNat 1, Int.negSucc 7, Int.ofNat 8]
]
private def V4top_g6 : List (List Int) := [
  [Int.ofNat 32, Int.ofNat 37, Int.ofNat 1, Int.negSucc 12, Int.ofNat 14, Int.negSucc 22, Int.ofNat 37, Int.ofNat 20, Int.negSucc 25, Int.ofNat 26, Int.negSucc 19, Int.ofNat 60, Int.ofNat 152, Int.ofNat 26, Int.negSucc 6, Int.negSucc 12, Int.negSucc 1, Int.ofNat 0, Int.ofNat 7, Int.negSucc 8, Int.negSucc 0, Int.negSucc 5, Int.negSucc 31, Int.ofNat 1, Int.ofNat 10, Int.ofNat 317, Int.negSucc 35, Int.negSucc 197, Int.negSucc 90, Int.negSucc 294, Int.ofNat 86, Int.ofNat 15, Int.negSucc 89, Int.ofNat 54],
  [Int.negSucc 59, Int.negSucc 36, Int.ofNat 4, Int.negSucc 7, Int.ofNat 8, Int.negSucc 2, Int.negSucc 24, Int.negSucc 8, Int.ofNat 31, Int.ofNat 29, Int.ofNat 3, Int.ofNat 25, Int.ofNat 49, Int.ofNat 20, Int.ofNat 4, Int.negSucc 23, Int.negSucc 4, Int.negSucc 8, Int.negSucc 20, Int.negSucc 14, Int.ofNat 3, Int.ofNat 0, Int.negSucc 17, Int.ofNat 26, Int.ofNat 12, Int.ofNat 389, Int.negSucc 43, Int.negSucc 205, Int.negSucc 108, Int.negSucc 280, Int.ofNat 74, Int.ofNat 10, Int.negSucc 84, Int.ofNat 61],
  [Int.ofNat 24, Int.negSucc 0, Int.negSucc 3, Int.negSucc 2, Int.ofNat 13, Int.ofNat 20, Int.ofNat 3, Int.ofNat 12, Int.ofNat 3, Int.negSucc 1, Int.ofNat 6, Int.ofNat 5, Int.ofNat 8, Int.negSucc 35, Int.ofNat 19, Int.ofNat 24, Int.negSucc 5, Int.negSucc 2, Int.negSucc 14, Int.ofNat 0, Int.ofNat 6, Int.negSucc 3, Int.negSucc 26, Int.ofNat 19, Int.ofNat 10, Int.ofNat 454, Int.negSucc 45, Int.negSucc 179, Int.negSucc 101, Int.negSucc 251, Int.ofNat 57, Int.ofNat 8, Int.negSucc 70, Int.ofNat 65],
  [Int.negSucc 6, Int.ofNat 14, Int.negSucc 2, Int.ofNat 22, Int.negSucc 18, Int.ofNat 16, Int.negSucc 11, Int.ofNat 0, Int.ofNat 8, Int.negSucc 31, Int.negSucc 3, Int.negSucc 24, Int.negSucc 63, Int.negSucc 16, Int.ofNat 2, Int.negSucc 3, Int.negSucc 19, Int.negSucc 13, Int.ofNat 14, Int.ofNat 12, Int.negSucc 1, Int.negSucc 2, Int.negSucc 13, Int.ofNat 15, Int.ofNat 13, Int.ofNat 370, Int.negSucc 39, Int.negSucc 159, Int.negSucc 78, Int.negSucc 215, Int.ofNat 55, Int.ofNat 8, Int.negSucc 55, Int.ofNat 56],
  [Int.negSucc 1, Int.negSucc 13, Int.negSucc 0, Int.negSucc 6, Int.negSucc 11, Int.negSucc 12, Int.negSucc 18, Int.ofNat 0, Int.negSucc 20, Int.negSucc 34, Int.ofNat 0, Int.negSucc 44, Int.negSucc 94, Int.ofNat 16, Int.negSucc 19, Int.negSucc 16, Int.negSucc 1, Int.negSucc 7, Int.ofNat 2, Int.ofNat 24, Int.negSucc 0, Int.ofNat 14, Int.negSucc 10, Int.ofNat 10, Int.ofNat 9, Int.ofNat 276, Int.negSucc 31, Int.negSucc 119, Int.negSucc 53, Int.negSucc 146, Int.ofNat 38, Int.ofNat 10, Int.negSucc 42, Int.ofNat 38],
  [Int.ofNat 30, Int.negSucc 10, Int.ofNat 18, Int.negSucc 5, Int.negSucc 20, Int.negSucc 16, Int.negSucc 4, Int.negSucc 13, Int.negSucc 29, Int.negSucc 29, Int.ofNat 0, Int.negSucc 37, Int.negSucc 70, Int.ofNat 10, Int.negSucc 14, Int.negSucc 7, Int.ofNat 8, Int.negSucc 11, Int.ofNat 1, Int.ofNat 19, Int.ofNat 4, Int.negSucc 11, Int.negSucc 2, Int.ofNat 6, Int.ofNat 2, Int.ofNat 156, Int.negSucc 21, Int.negSucc 69, Int.negSucc 27, Int.negSucc 81, Int.ofNat 25, Int.ofNat 2, Int.negSucc 23, Int.ofNat 20],
  [Int.ofNat 29, Int.negSucc 5, Int.ofNat 11, Int.ofNat 6, Int.negSucc 14, Int.ofNat 4, Int.ofNat 11, Int.negSucc 13, Int.negSucc 6, Int.negSucc 9, Int.negSucc 5, Int.negSucc 2, Int.negSucc 24, Int.ofNat 3, Int.negSucc 9, Int.negSucc 0, Int.ofNat 4, Int.negSucc 2, Int.ofNat 1, Int.ofNat 6, Int.ofNat 3, Int.negSucc 2, Int.ofNat 3, Int.ofNat 2, Int.ofNat 1, Int.ofNat 53, Int.negSucc 6, Int.negSucc 21, Int.negSucc 8, Int.negSucc 24, Int.ofNat 8, Int.ofNat 1, Int.negSucc 7, Int.ofNat 6]
]
private def V4top : List (List Int) := V4top_g0 ++ V4top_g1 ++ V4top_g2 ++ V4top_g3 ++ V4top_g4 ++ V4top_g5 ++ V4top_g6

private def V4bot_g0 : List (List Int) := [
  [Int.ofNat 12, Int.negSucc 16, Int.negSucc 8, Int.ofNat 17, Int.negSucc 5, Int.ofNat 27, Int.ofNat 22, Int.ofNat 16, Int.ofNat 5, Int.ofNat 156, Int.negSucc 76, Int.negSucc 27, Int.ofNat 41, Int.ofNat 133, Int.negSucc 20, Int.negSucc 43, Int.ofNat 72, Int.ofNat 89, Int.ofNat 205, Int.ofNat 145, Int.negSucc 84, Int.ofNat 19, Int.ofNat 124, Int.negSucc 14, Int.negSucc 3, Int.negSucc 6, Int.negSucc 241, Int.ofNat 161, Int.ofNat 59, Int.negSucc 351, Int.ofNat 154, Int.ofNat 6, Int.ofNat 165, Int.negSucc 776],
  [Int.ofNat 13, Int.negSucc 6, Int.ofNat 31, Int.negSucc 36, Int.ofNat 43, Int.negSucc 10, Int.negSucc 29, Int.negSucc 7, Int.ofNat 6, Int.negSucc 64, Int.ofNat 27, Int.negSucc 26, Int.ofNat 28, Int.ofNat 36, Int.negSucc 82, Int.ofNat 107, Int.ofNat 7, Int.ofNat 79, Int.ofNat 160, Int.negSucc 12, Int.ofNat 7, Int.negSucc 9, Int.ofNat 40, Int.negSucc 4, Int.ofNat 2, Int.ofNat 8, Int.negSucc 90, Int.ofNat 89, Int.ofNat 17, Int.negSucc 257, Int.ofNat 132, Int.ofNat 47, Int.ofNat 134, Int.negSucc 935],
  [Int.negSucc 6, Int.ofNat 11, Int.negSucc 6, Int.ofNat 8, Int.negSucc 8, Int.negSucc 42, Int.ofNat 16, Int.ofNat 8, Int.negSucc 3, Int.negSucc 66, Int.ofNat 97, Int.ofNat 59, Int.negSucc 39, Int.negSucc 24, Int.ofNat 84, Int.ofNat 125, Int.negSucc 62, Int.negSucc 0, Int.ofNat 70, Int.ofNat 82, Int.negSucc 9, Int.ofNat 10, Int.ofNat 5, Int.negSucc 5, Int.ofNat 4, Int.ofNat 7, Int.negSucc 7, Int.ofNat 0, Int.ofNat 42, Int.negSucc 176, Int.ofNat 107, Int.ofNat 47, Int.ofNat 193, Int.negSucc 1040],
  [Int.ofNat 2, Int.ofNat 14, Int.negSucc 12, Int.negSucc 0, Int.ofNat 6, Int.ofNat 0, Int.negSucc 14, Int.ofNat 7, Int.negSucc 2, Int.ofNat 33, Int.ofNat 55, Int.ofNat 0, Int.negSucc 14, Int.negSucc 189, Int.ofNat 25, Int.ofNat 31, Int.negSucc 29, Int.negSucc 1, Int.ofNat 4, Int.ofNat 4, Int.negSucc 7, Int.ofNat 18, Int.negSucc 14, Int.negSucc 63, Int.negSucc 2, Int.ofNat 17, Int.ofNat 53, Int.negSucc 79, Int.ofNat 77, Int.negSucc 70, Int.ofNat 86, Int.ofNat 42, Int.ofNat 267, Int.negSucc 1118],
  [Int.negSucc 1, Int.negSucc 9, Int.negSucc 1, Int.ofNat 6, Int.negSucc 5, Int.ofNat 26, Int.ofNat 11, Int.negSucc 13, Int.ofNat 41, Int.ofNat 13, Int.ofNat 10, Int.negSucc 40, Int.ofNat 27, Int.negSucc 107, Int.ofNat 49, Int.negSucc 21, Int.negSucc 15, Int.negSucc 15, Int.negSucc 47, Int.negSucc 30, Int.ofNat 3, Int.ofNat 19, Int.negSucc 27, Int.negSucc 97, Int.negSucc 7, Int.ofNat 9, Int.ofNat 33, Int.negSucc 82, Int.ofNat 111, Int.ofNat 26, Int.ofNat 71, Int.ofNat 37, Int.ofNat 316, Int.negSucc 1151],
  [Int.negSucc 11, Int.negSucc 2, Int.ofNat 0, Int.ofNat 1, Int.negSucc 13, Int.ofNat 9, Int.negSucc 5, Int.negSucc 15, Int.ofNat 28, Int.negSucc 16, Int.negSucc 45, Int.ofNat 38, Int.ofNat 43, Int.ofNat 23, Int.ofNat 5, Int.negSucc 54, Int.ofNat 12, Int.negSucc 36, Int.negSucc 103, Int.negSucc 48, Int.ofNat 15, Int.negSucc 16, Int.negSucc 47, Int.negSucc 124, Int.negSucc 14, Int.ofNat 0, Int.ofNat 18, Int.negSucc 27, Int.ofNat 137, Int.ofNat 78, Int.ofNat 63, Int.ofNat 25, Int.ofNat 340, Int.negSucc 1176],
  [Int.negSucc 8, Int.ofNat 0, Int.ofNat 3, Int.ofNat 1, Int.negSucc 1, Int.negSucc 9, Int.ofNat 9, Int.ofNat 20, Int.negSucc 62, Int.negSucc 32, Int.negSucc 65, Int.ofNat 7, Int.negSucc 75, Int.ofNat 151, Int.negSucc 61, Int.negSucc 82, Int.ofNat 13, Int.negSucc 69, Int.negSucc 142, Int.negSucc 59, Int.ofNat 42, Int.negSucc 27, Int.negSucc 69, Int.negSucc 143, Int.negSucc 20, Int.negSucc 34, Int.ofNat 48, Int.negSucc 11, Int.ofNat 152, Int.ofNat 106, Int.ofNat 62, Int.ofNat 22, Int.ofNat 343, Int.negSucc 1184]
]
private def V4bot_g1 : List (List Int) := [
  [Int.ofNat 19, Int.negSucc 4, Int.negSucc 32, Int.negSucc 24, Int.ofNat 37, Int.negSucc 85, Int.negSucc 1, Int.negSucc 16, Int.ofNat 74, Int.ofNat 13, Int.ofNat 32, Int.ofNat 43, Int.negSucc 5, Int.negSucc 10, Int.ofNat 15, Int.negSucc 177, Int.ofNat 67, Int.negSucc 29, Int.negSucc 172, Int.negSucc 21, Int.ofNat 21, Int.ofNat 19, Int.ofNat 55, Int.ofNat 145, Int.ofNat 19, Int.negSucc 4, Int.negSucc 92, Int.ofNat 87, Int.negSucc 128, Int.negSucc 96, Int.negSucc 21, Int.ofNat 20, Int.ofNat 63, Int.negSucc 179],
  [Int.negSucc 3, Int.ofNat 14, Int.ofNat 10, Int.ofNat 15, Int.negSucc 17, Int.ofNat 5, Int.ofNat 45, Int.negSucc 6, Int.ofNat 14, Int.negSucc 20, Int.ofNat 88, Int.ofNat 37, Int.ofNat 5, Int.negSucc 22, Int.ofNat 12, Int.negSucc 220, Int.ofNat 22, Int.negSucc 53, Int.negSucc 101, Int.negSucc 7, Int.ofNat 1, Int.ofNat 13, Int.ofNat 12, Int.ofNat 221, Int.ofNat 32, Int.negSucc 1, Int.negSucc 41, Int.ofNat 71, Int.negSucc 175, Int.negSucc 69, Int.negSucc 59, Int.ofNat 4, Int.ofNat 94, Int.negSucc 237],
  [Int.negSucc 3, Int.negSucc 25, Int.ofNat 27, Int.ofNat 4, Int.ofNat 12, Int.ofNat 74, Int.negSucc 27, Int.ofNat 10, Int.negSucc 51, Int.negSucc 1, Int.ofNat 0, Int.negSucc 14, Int.ofNat 13, Int.negSucc 29, Int.ofNat 3, Int.negSucc 167, Int.ofNat 26, Int.negSucc 18, Int.negSucc 13, Int.negSucc 11, Int.negSucc 4, Int.ofNat 6, Int.ofNat 28, Int.ofNat 262, Int.ofNat 33, Int.ofNat 3, Int.negSucc 10, Int.ofNat 60, Int.negSucc 224, Int.negSucc 44, Int.negSucc 87, Int.negSucc 13, Int.ofNat 135, Int.negSucc 278],
  [Int.ofNat 26, Int.negSucc 0, Int.ofNat 0, Int.ofNat 22, Int.negSucc 54, Int.negSucc 11, Int.negSucc 20, Int.ofNat 45, Int.ofNat 6, Int.negSucc 40, Int.negSucc 54, Int.negSucc 31, Int.ofNat 11, Int.negSucc 5, Int.negSucc 3, Int.negSucc 33, Int.ofNat 7, Int.ofNat 10, Int.negSucc 2, Int.negSucc 4, Int.ofNat 14, Int.ofNat 6, Int.ofNat 68, Int.ofNat 287, Int.ofNat 31, Int.ofNat 7, Int.ofNat 23, Int.ofNat 32, Int.negSucc 231, Int.negSucc 3, Int.negSucc 128, Int.negSucc 9, Int.ofNat 164, Int.negSucc 309],
  [Int.ofNat 1, Int.ofNat 47, Int.negSucc 16, Int.ofNat 11, Int.ofNat 3, Int.ofNat 0, Int.negSucc 20, Int.ofNat 46, Int.ofNat 22, Int.negSucc 11, Int.negSucc 47, Int.negSucc 32, Int.ofNat 4, Int.ofNat 12, Int.negSucc 7, Int.ofNat 47, Int.negSucc 6, Int.ofNat 10, Int.ofNat 0, Int.negSucc 9, Int.ofNat 4, Int.ofNat 6, Int.ofNat 73, Int.ofNat 305, Int.ofNat 29, Int.ofNat 4, Int.negSucc 7, Int.ofNat 9, Int.negSucc 209, Int.ofNat 46, Int.negSucc 133, Int.negSucc 8, Int.ofNat 186, Int.negSucc 333],
  [Int.negSucc 15, Int.ofNat 34, Int.negSucc 6, Int.ofNat 1, Int.ofNat 17, Int.ofNat 15, Int.ofNat 3, Int.ofNat 0, Int.negSucc 20, Int.ofNat 10, Int.negSucc 29, Int.ofNat 1, Int.negSucc 5, Int.ofNat 3, Int.ofNat 1, Int.ofNat 115, Int.negSucc 28, Int.ofNat 8, Int.ofNat 18, Int.negSucc 37, Int.ofNat 9, Int.ofNat 3, Int.ofNat 86, Int.ofNat 325, Int.ofNat 27, Int.ofNat 5, Int.negSucc 3, Int.ofNat 43, Int.negSucc 185, Int.ofNat 86, Int.negSucc 140, Int.negSucc 12, Int.ofNat 201, Int.negSucc 346],
  [Int.negSucc 1, Int.negSucc 35, Int.ofNat 5, Int.negSucc 17, Int.negSucc 1, Int.negSucc 12, Int.ofNat 22, Int.negSucc 99, Int.negSucc 21, Int.ofNat 35, Int.negSucc 0, Int.ofNat 0, Int.negSucc 21, Int.ofNat 27, Int.negSucc 4, Int.ofNat 118, Int.negSucc 62, Int.ofNat 5, Int.ofNat 43, Int.negSucc 50, Int.ofNat 10, Int.negSucc 18, Int.ofNat 95, Int.ofNat 369, Int.ofNat 33, Int.negSucc 36, Int.ofNat 9, Int.ofNat 56, Int.negSucc 183, Int.ofNat 104, Int.negSucc 143, Int.negSucc 14, Int.ofNat 201, Int.negSucc 348]
]
private def V4bot_g2 : List (List Int) := [
  [Int.negSucc 2, Int.negSucc 4, Int.ofNat 36, Int.ofNat 9, Int.negSucc 9, Int.ofNat 38, Int.ofNat 22, Int.ofNat 21, Int.negSucc 9, Int.ofNat 28, Int.ofNat 15, Int.ofNat 17, Int.negSucc 23, Int.negSucc 42, Int.ofNat 24, Int.ofNat 166, Int.ofNat 126, Int.ofNat 19, Int.negSucc 328, Int.negSucc 19, Int.ofNat 22, Int.ofNat 35, Int.ofNat 27, Int.negSucc 27, Int.negSucc 27, Int.ofNat 11, Int.negSucc 96, Int.ofNat 73, Int.negSucc 106, Int.negSucc 116, Int.negSucc 112, Int.negSucc 39, Int.ofNat 169, Int.ofNat 24],
  [Int.ofNat 26, Int.negSucc 11, Int.negSucc 2, Int.ofNat 8, Int.ofNat 21, Int.ofNat 21, Int.negSucc 26, Int.negSucc 8, Int.negSucc 8, Int.ofNat 29, Int.negSucc 23, Int.ofNat 4, Int.negSucc 4, Int.negSucc 26, Int.negSucc 1, Int.ofNat 154, Int.ofNat 81, Int.ofNat 14, Int.negSucc 214, Int.ofNat 47, Int.negSucc 41, Int.ofNat 39, Int.negSucc 27, Int.negSucc 86, Int.negSucc 24, Int.ofNat 17, Int.negSucc 80, Int.ofNat 86, Int.negSucc 207, Int.negSucc 100, Int.negSucc 200, Int.negSucc 83, Int.ofNat 233, Int.ofNat 30],
  [Int.negSucc 10, Int.ofNat 14, Int.negSucc 28, Int.ofNat 3, Int.negSucc 18, Int.negSucc 27, Int.ofNat 20, Int.negSucc 2, Int.ofNat 23, Int.negSucc 17, Int.negSucc 66, Int.negSucc 10, Int.ofNat 0, Int.negSucc 1, Int.negSucc 5, Int.ofNat 74, Int.ofNat 68, Int.ofNat 41, Int.negSucc 74, Int.ofNat 31, Int.negSucc 20, Int.negSucc 5, Int.negSucc 68, Int.negSucc 147, Int.negSucc 26, Int.ofNat 21, Int.negSucc 51, Int.ofNat 90, Int.negSucc 273, Int.negSucc 84, Int.negSucc 268, Int.negSucc 111, Int.ofNat 281, Int.ofNat 34],
  [Int.negSucc 5, Int.negSucc 6, Int.ofNat 4, Int.negSucc 23, Int.ofNat 7, Int.negSucc 5, Int.negSucc 11, Int.negSucc 18, Int.negSucc 0, Int.negSucc 51, Int.negSucc 48, Int.negSucc 15, Int.ofNat 12, Int.ofNat 48, Int.negSucc 15, Int.negSucc 0, Int.ofNat 44, Int.ofNat 23, Int.ofNat 26, Int.ofNat 33, Int.negSucc 11, Int.negSucc 8, Int.negSucc 8, Int.negSucc 194, Int.negSucc 14, Int.ofNat 22, Int.negSucc 34, Int.ofNat 81, Int.negSucc 343, Int.negSucc 43, Int.negSucc 309, Int.negSucc 117, Int.ofNat 307, Int.ofNat 14],
  [Int.ofNat 5, Int.ofNat 12, Int.ofNat 11, Int.negSucc 36, Int.ofNat 10, Int.negSucc 17, Int.negSucc 18, Int.negSucc 25, Int.negSucc 6, Int.negSucc 41, Int.negSucc 8, Int.ofNat 8, Int.negSucc 4, Int.ofNat 33, Int.negSucc 8, Int.negSucc 29, Int.ofNat 9, Int.ofNat 10, Int.ofNat 63, Int.ofNat 15, Int.ofNat 6, Int.negSucc 20, Int.ofNat 0, Int.negSucc 178, Int.negSucc 7, Int.ofNat 17, Int.negSucc 73, Int.ofNat 69, Int.negSucc 371, Int.ofNat 3, Int.negSucc 337, Int.negSucc 129, Int.ofNat 328, Int.negSucc 3],
  [Int.ofNat 5, Int.ofNat 10, Int.ofNat 8, Int.ofNat 11, Int.negSucc 0, Int.negSucc 9, Int.ofNat 6, Int.ofNat 2, Int.negSucc 0, Int.ofNat 9, Int.ofNat 53, Int.ofNat 10, Int.ofNat 0, Int.negSucc 7, Int.ofNat 5, Int.negSucc 63, Int.negSucc 30, Int.negSucc 1, Int.ofNat 86, Int.ofNat 2, Int.negSucc 5, Int.negSucc 11, Int.negSucc 0, Int.negSucc 187, Int.negSucc 6, Int.ofNat 23, Int.negSucc 68, Int.ofNat 111, Int.negSucc 371, Int.ofNat 36, Int.negSucc 349, Int.negSucc 126, Int.ofNat 344, Int.negSucc 9],
  [Int.negSucc 20, Int.negSucc 4, Int.negSucc 11, Int.ofNat 29, Int.negSucc 2, Int.ofNat 17, Int.ofNat 10, Int.ofNat 25, Int.negSucc 1, Int.ofNat 51, Int.ofNat 72, Int.ofNat 1, Int.negSucc 2, Int.negSucc 23, Int.ofNat 18, Int.negSucc 59, Int.negSucc 35, Int.negSucc 1, Int.ofNat 98, Int.ofNat 2, Int.negSucc 33, Int.negSucc 26, Int.negSucc 4, Int.negSucc 213, Int.negSucc 8, Int.negSucc 25, Int.negSucc 64, Int.ofNat 132, Int.negSucc 393, Int.ofNat 52, Int.negSucc 362, Int.negSucc 129, Int.ofNat 347, Int.negSucc 8]
]
private def V4bot_g3 : List (List Int) := [
  [Int.ofNat 6, Int.negSucc 29, Int.ofNat 20, Int.ofNat 29, Int.negSucc 6, Int.ofNat 8, Int.negSucc 5, Int.ofNat 46, Int.ofNat 2, Int.ofNat 1, Int.negSucc 46, Int.negSucc 15, Int.negSucc 0, Int.negSucc 56, Int.ofNat 27, Int.ofNat 34, Int.negSucc 148, Int.negSucc 89, Int.ofNat 51, Int.negSucc 193, Int.ofNat 387, Int.negSucc 116, Int.ofNat 113, Int.negSucc 60, Int.negSucc 10, Int.ofNat 3, Int.negSucc 69, Int.ofNat 38, Int.ofNat 34, Int.negSucc 124, Int.negSucc 24, Int.negSucc 182, Int.ofNat 352, Int.ofNat 203],
  [Int.ofNat 10, Int.negSucc 0, Int.negSucc 12, Int.negSucc 22, Int.negSucc 4, Int.ofNat 2, Int.ofNat 8, Int.negSucc 4, Int.ofNat 14, Int.ofNat 22, Int.negSucc 44, Int.negSucc 3, Int.ofNat 8, Int.negSucc 21, Int.ofNat 12, Int.negSucc 17, Int.negSucc 123, Int.negSucc 93, Int.ofNat 48, Int.negSucc 32, Int.ofNat 284, Int.negSucc 60, Int.ofNat 46, Int.negSucc 19, Int.negSucc 9, Int.ofNat 2, Int.negSucc 41, Int.ofNat 14, Int.ofNat 102, Int.negSucc 146, Int.negSucc 69, Int.negSucc 247, Int.ofNat 442, Int.ofNat 244],
  [Int.negSucc 10, Int.ofNat 52, Int.negSucc 24, Int.negSucc 8, Int.ofNat 18, Int.negSucc 7, Int.negSucc 4, Int.negSucc 36, Int.ofNat 12, Int.negSucc 6, Int.negSucc 22, Int.ofNat 3, Int.negSucc 4, Int.ofNat 0, Int.negSucc 5, Int.negSucc 15, Int.negSucc 19, Int.negSucc 19, Int.ofNat 22, Int.negSucc 45, Int.ofNat 130, Int.negSucc 28, Int.negSucc 27, Int.ofNat 44, Int.negSucc 0, Int.ofNat 2, Int.ofNat 10, Int.negSucc 29, Int.ofNat 203, Int.negSucc 170, Int.negSucc 101, Int.negSucc 307, Int.ofNat 508, Int.ofNat 271],
  [Int.negSucc 22, Int.ofNat 10, Int.negSucc 0, Int.negSucc 3, Int.ofNat 14, Int.ofNat 23, Int.ofNat 29, Int.negSucc 35, Int.negSucc 17, Int.negSucc 18, Int.ofNat 29, Int.ofNat 4, Int.ofNat 1, Int.ofNat 58, Int.negSucc 14, Int.negSucc 28, Int.ofNat 8, Int.negSucc 5, Int.negSucc 3, Int.ofNat 6, Int.ofNat 10, Int.ofNat 12, Int.negSucc 2, Int.ofNat 52, Int.negSucc 1, Int.ofNat 5, Int.ofNat 55, Int.negSucc 76, Int.ofNat 267, Int.negSucc 175, Int.negSucc 148, Int.negSucc 353, Int.ofNat 557, Int.ofNat 276],
  [Int.negSucc 19, Int.negSucc 5, Int.ofNat 16, Int.ofNat 21, Int.negSucc 17, Int.ofNat 1, Int.ofNat 9, Int.negSucc 14, Int.negSucc 39, Int.negSucc 2, Int.ofNat 32, Int.ofNat 26, Int.negSucc 6, Int.ofNat 37, Int.negSucc 10, Int.negSucc 12, Int.ofNat 38, Int.ofNat 26, Int.negSucc 1, Int.ofNat 32, Int.negSucc 60, Int.ofNat 41, Int.negSucc 7, Int.ofNat 66, Int.ofNat 3, Int.ofNat 1, Int.ofNat 18, Int.negSucc 94, Int.ofNat 304, Int.negSucc 167, Int.negSucc 187, Int.negSucc 389, Int.ofNat 594, Int.ofNat 279],
  [Int.ofNat 8, Int.negSucc 16, Int.ofNat 5, Int.negSucc 4, Int.negSucc 6, Int.negSucc 10, Int.negSucc 17, Int.ofNat 12, Int.ofNat 5, Int.ofNat 0, Int.ofNat 19, Int.negSucc 5, Int.negSucc 8, Int.negSucc 6, Int.negSucc 1, Int.ofNat 4, Int.ofNat 54, Int.ofNat 46, Int.negSucc 11, Int.ofNat 43, Int.negSucc 101, Int.ofNat 73, Int.ofNat 4, Int.ofNat 73, Int.ofNat 5, Int.ofNat 3, Int.ofNat 17, Int.negSucc 53, Int.ofNat 327, Int.negSucc 158, Int.negSucc 212, Int.negSucc 403, Int.ofNat 615, Int.ofNat 280],
  [Int.ofNat 31, Int.negSucc 9, Int.ofNat 2, Int.negSucc 12, Int.ofNat 9, Int.negSucc 17, Int.negSucc 18, Int.ofNat 44, Int.ofNat 31, Int.ofNat 5, Int.ofNat 26, Int.negSucc 10, Int.ofNat 15, Int.negSucc 24, Int.ofNat 5, Int.ofNat 1, Int.ofNat 51, Int.ofNat 49, Int.negSucc 8, Int.ofNat 48, Int.negSucc 108, Int.ofNat 70, Int.negSucc 0, Int.ofNat 83, Int.ofNat 5, Int.negSucc 32, Int.ofNat 24, Int.negSucc 51, Int.ofNat 351, Int.negSucc 157, Int.negSucc 223, Int.negSucc 418, Int.ofNat 624, Int.ofNat 286]
]
private def V4bot_g4 : List (List Int) := [
  [Int.ofNat 12, Int.negSucc 12, Int.negSucc 7, Int.negSucc 21, Int.negSucc 15, Int.negSucc 10, Int.ofNat 12, Int.ofNat 2, Int.ofNat 8, Int.negSucc 47, Int.negSucc 68, Int.negSucc 12, Int.negSucc 10, Int.negSucc 57, Int.ofNat 20, Int.negSucc 14, Int.negSucc 136, Int.negSucc 77, Int.ofNat 19, Int.negSucc 205, Int.negSucc 407, Int.negSucc 207, Int.ofNat 86, Int.negSucc 32, Int.ofNat 22, Int.ofNat 3, Int.negSucc 52, Int.ofNat 33, Int.ofNat 1, Int.negSucc 47, Int.ofNat 144, Int.ofNat 41, Int.ofNat 377, Int.ofNat 239],
  [Int.negSucc 15, Int.ofNat 16, Int.ofNat 35, Int.ofNat 26, Int.ofNat 27, Int.ofNat 11, Int.negSucc 8, Int.ofNat 0, Int.negSucc 2, Int.ofNat 0, Int.negSucc 36, Int.ofNat 7, Int.ofNat 8, Int.negSucc 12, Int.ofNat 9, Int.ofNat 8, Int.negSucc 82, Int.negSucc 87, Int.negSucc 8, Int.negSucc 73, Int.negSucc 262, Int.negSucc 151, Int.ofNat 22, Int.negSucc 8, Int.ofNat 39, Int.ofNat 1, Int.negSucc 27, Int.ofNat 29, Int.negSucc 32, Int.negSucc 5, Int.ofNat 245, Int.ofNat 75, Int.ofNat 453, Int.ofNat 268],
  [Int.negSucc 19, Int.ofNat 25, Int.negSucc 0, Int.negSucc 7, Int.negSucc 16, Int.ofNat 7, Int.ofNat 7, Int.ofNat 14, Int.negSucc 6, Int.ofNat 34, Int.ofNat 7, Int.ofNat 3, Int.negSucc 3, Int.ofNat 12, Int.ofNat 10, Int.ofNat 15, Int.negSucc 38, Int.ofNat 0, Int.negSucc 27, Int.negSucc 67, Int.negSucc 89, Int.negSucc 51, Int.negSucc 16, Int.negSucc 2, Int.negSucc 12, Int.ofNat 6, Int.negSucc 3, Int.ofNat 27, Int.negSucc 97, Int.ofNat 47, Int.ofNat 374, Int.ofNat 94, Int.ofNat 507, Int.ofNat 278],
  [Int.ofNat 30, Int.negSucc 20, Int.negSucc 40, Int.ofNat 9, Int.ofNat 7, Int.ofNat 11, Int.negSucc 8, Int.negSucc 4, Int.ofNat 9, Int.ofNat 30, Int.ofNat 24, Int.ofNat 9, Int.ofNat 1, Int.ofNat 35, Int.negSucc 7, Int.ofNat 24, Int.ofNat 2, Int.negSucc 3, Int.negSucc 27, Int.ofNat 2, Int.negSucc 4, Int.negSucc 9, Int.ofNat 0, Int.negSucc 9, Int.ofNat 0, Int.ofNat 9, Int.ofNat 3, Int.ofNat 17, Int.negSucc 130, Int.ofNat 91, Int.ofNat 473, Int.ofNat 109, Int.ofNat 562, Int.ofNat 292],
  [Int.ofNat 10, Int.negSucc 21, Int.negSucc 30, Int.ofNat 3, Int.ofNat 2, Int.negSucc 9, Int.negSucc 8, Int.negSucc 1, Int.negSucc 14, Int.ofNat 7, Int.ofNat 23, Int.ofNat 18, Int.negSucc 10, Int.ofNat 11, Int.ofNat 1, Int.ofNat 7, Int.ofNat 36, Int.ofNat 24, Int.ofNat 1, Int.ofNat 34, Int.ofNat 63, Int.ofNat 28, Int.negSucc 18, Int.ofNat 7, Int.ofNat 4, Int.ofNat 9, Int.negSucc 6, Int.ofNat 20, Int.negSucc 148, Int.ofNat 122, Int.ofNat 527, Int.ofNat 118, Int.ofNat 602, Int.ofNat 303],
  [Int.ofNat 2, Int.ofNat 1, Int.ofNat 11, Int.negSucc 11, Int.negSucc 9, Int.negSucc 8, Int.ofNat 0, Int.negSucc 6, Int.ofNat 5, Int.negSucc 14, Int.ofNat 14, Int.ofNat 2, Int.ofNat 2, Int.negSucc 13, Int.negSucc 8, Int.negSucc 2, Int.ofNat 55, Int.ofNat 38, Int.ofNat 4, Int.ofNat 66, Int.ofNat 98, Int.ofNat 64, Int.ofNat 1, Int.ofNat 5, Int.ofNat 4, Int.ofNat 4, Int.ofNat 4, Int.ofNat 28, Int.negSucc 154, Int.ofNat 139, Int.ofNat 557, Int.ofNat 125, Int.ofNat 626, Int.ofNat 311],
  [Int.negSucc 15, Int.ofNat 15, Int.ofNat 40, Int.negSucc 1, Int.ofNat 4, Int.ofNat 0, Int.ofNat 12, Int.ofNat 4, Int.ofNat 0, Int.negSucc 20, Int.ofNat 25, Int.negSucc 17, Int.ofNat 8, Int.ofNat 4, Int.negSucc 9, Int.negSucc 13, Int.ofNat 69, Int.ofNat 55, Int.ofNat 16, Int.ofNat 91, Int.ofNat 96, Int.ofNat 59, Int.negSucc 4, Int.ofNat 7, Int.ofNat 4, Int.negSucc 11, Int.negSucc 1, Int.ofNat 27, Int.negSucc 158, Int.ofNat 154, Int.ofNat 588, Int.ofNat 128, Int.ofNat 634, Int.ofNat 314]
]
private def V4bot_g5 : List (List Int) := [
  [Int.ofNat 13, Int.negSucc 10, Int.negSucc 27, Int.negSucc 21, Int.negSucc 10, Int.ofNat 24, Int.ofNat 11, Int.negSucc 13, Int.negSucc 21, Int.negSucc 23, Int.negSucc 57, Int.negSucc 8, Int.negSucc 1, Int.negSucc 12, Int.ofNat 16, Int.negSucc 13, Int.negSucc 72, Int.negSucc 34, Int.ofNat 49, Int.negSucc 141, Int.negSucc 43, Int.ofNat 517, Int.negSucc 3, Int.negSucc 42, Int.ofNat 33, Int.negSucc 0, Int.negSucc 27, Int.ofNat 21, Int.negSucc 3, Int.negSucc 49, Int.negSucc 82, Int.ofNat 348, Int.ofNat 167, Int.ofNat 124],
  [Int.negSucc 16, Int.ofNat 17, Int.ofNat 31, Int.ofNat 14, Int.ofNat 4, Int.negSucc 12, Int.ofNat 9, Int.ofNat 7, Int.ofNat 14, Int.negSucc 19, Int.negSucc 27, Int.ofNat 1, Int.ofNat 2, Int.negSucc 4, Int.negSucc 0, Int.ofNat 10, Int.negSucc 23, Int.negSucc 86, Int.ofNat 37, Int.negSucc 72, Int.negSucc 20, Int.ofNat 376, Int.negSucc 24, Int.negSucc 26, Int.ofNat 14, Int.negSucc 0, Int.negSucc 12, Int.ofNat 11, Int.ofNat 24, Int.negSucc 55, Int.negSucc 104, Int.ofNat 444, Int.ofNat 198, Int.ofNat 131],
  [Int.negSucc 1, Int.ofNat 5, Int.negSucc 25, Int.negSucc 3, Int.negSucc 16, Int.negSucc 0, Int.negSucc 15, Int.ofNat 7, Int.ofNat 0, Int.ofNat 34, Int.ofNat 31, Int.negSucc 2, Int.ofNat 5, Int.ofNat 23, Int.negSucc 3, Int.ofNat 4, Int.negSucc 7, Int.negSucc 42, Int.ofNat 23, Int.negSucc 65, Int.negSucc 3, Int.ofNat 140, Int.negSucc 15, Int.ofNat 0, Int.negSucc 58, Int.ofNat 0, Int.ofNat 0, Int.negSucc 2, Int.ofNat 56, Int.negSucc 75, Int.negSucc 181, Int.ofNat 560, Int.ofNat 212, Int.ofNat 131],
  [Int.ofNat 5, Int.negSucc 11, Int.ofNat 43, Int.negSucc 4, Int.ofNat 6, Int.negSucc 16, Int.negSucc 13, Int.ofNat 12, Int.ofNat 24, Int.ofNat 39, Int.ofNat 14, Int.ofNat 16, Int.negSucc 10, Int.ofNat 7, Int.ofNat 5, Int.ofNat 2, Int.ofNat 8, Int.negSucc 34, Int.ofNat 12, Int.negSucc 13, Int.ofNat 19, Int.negSucc 2, Int.ofNat 9, Int.ofNat 17, Int.negSucc 104, Int.ofNat 0, Int.ofNat 1, Int.negSucc 16, Int.ofNat 88, Int.negSucc 85, Int.negSucc 219, Int.ofNat 647, Int.ofNat 235, Int.ofNat 137],
  [Int.negSucc 9, Int.ofNat 6, Int.ofNat 37, Int.negSucc 5, Int.ofNat 7, Int.negSucc 9, Int.ofNat 12, Int.ofNat 2, Int.ofNat 3, Int.ofNat 23, Int.ofNat 14, Int.ofNat 6, Int.negSucc 2, Int.ofNat 2, Int.negSucc 4, Int.negSucc 10, Int.ofNat 18, Int.ofNat 14, Int.negSucc 1, Int.ofNat 28, Int.ofNat 21, Int.negSucc 103, Int.ofNat 9, Int.ofNat 28, Int.negSucc 131, Int.ofNat 1, Int.ofNat 0, Int.negSucc 20, Int.ofNat 104, Int.negSucc 89, Int.negSucc 238, Int.ofNat 710, Int.ofNat 256, Int.ofNat 146],
  [Int.ofNat 6, Int.negSucc 2, Int.negSucc 5, Int.ofNat 7, Int.negSucc 0, Int.ofNat 10, Int.ofNat 6, Int.negSucc 9, Int.negSucc 6, Int.negSucc 17, Int.ofNat 8, Int.ofNat 5, Int.ofNat 7, Int.negSucc 3, Int.negSucc 1, Int.negSucc 1, Int.ofNat 22, Int.ofNat 32, Int.negSucc 5, Int.ofNat 48, Int.ofNat 26, Int.negSucc 161, Int.ofNat 12, Int.ofNat 26, Int.negSucc 150, Int.ofNat 4, Int.ofNat 5, Int.negSucc 17, Int.ofNat 121, Int.negSucc 92, Int.negSucc 257, Int.ofNat 757, Int.ofNat 270, Int.ofNat 151],
  [Int.ofNat 4, Int.negSucc 4, Int.negSucc 51, Int.ofNat 6, Int.ofNat 0, Int.ofNat 13, Int.negSucc 2, Int.negSucc 2, Int.negSucc 17, Int.negSucc 31, Int.ofNat 11, Int.negSucc 13, Int.ofNat 1, Int.ofNat 3, Int.negSucc 2, Int.negSucc 1, Int.ofNat 26, Int.ofNat 37, Int.negSucc 7, Int.ofNat 61, Int.ofNat 37, Int.negSucc 194, Int.ofNat 15, Int.ofNat 27, Int.negSucc 164, Int.ofNat 0, Int.ofNat 4, Int.negSucc 22, Int.ofNat 130, Int.negSucc 93, Int.negSucc 268, Int.ofNat 776, Int.ofNat 274, Int.ofNat 153]
]
private def V4bot_g6 : List (List Int) := [
  [Int.ofNat 4, Int.negSucc 5, Int.ofNat 27, Int.ofNat 70, Int.ofNat 62, Int.negSucc 35, Int.negSucc 5, Int.negSucc 7, Int.ofNat 1, Int.negSucc 27, Int.negSucc 34, Int.negSucc 2, Int.ofNat 1, Int.ofNat 1, Int.ofNat 0, Int.negSucc 48, Int.negSucc 238, Int.ofNat 277, Int.negSucc 89, Int.ofNat 37, Int.ofNat 3, Int.ofNat 76, Int.negSucc 6, Int.negSucc 18, Int.ofNat 98, Int.negSucc 3, Int.negSucc 2, Int.ofNat 1, Int.ofNat 10, Int.negSucc 13, Int.negSucc 23, Int.ofNat 91, Int.ofNat 42, Int.ofNat 31],
  [Int.negSucc 3, Int.ofNat 0, Int.negSucc 3, Int.negSucc 8, Int.negSucc 7, Int.ofNat 8, Int.ofNat 7, Int.ofNat 1, Int.ofNat 2, Int.negSucc 5, Int.negSucc 4, Int.negSucc 2, Int.ofNat 3, Int.ofNat 13, Int.negSucc 12, Int.negSucc 33, Int.negSucc 221, Int.ofNat 280, Int.negSucc 105, Int.ofNat 60, Int.ofNat 9, Int.ofNat 3, Int.negSucc 10, Int.negSucc 26, Int.ofNat 173, Int.negSucc 5, Int.negSucc 0, Int.ofNat 0, Int.ofNat 16, Int.negSucc 18, Int.negSucc 38, Int.ofNat 113, Int.ofNat 48, Int.ofNat 30],
  [Int.ofNat 4, Int.negSucc 1, Int.negSucc 22, Int.negSucc 25, Int.negSucc 25, Int.ofNat 13, Int.negSucc 7, Int.ofNat 2, Int.ofNat 1, Int.ofNat 17, Int.ofNat 3, Int.ofNat 3, Int.negSucc 4, Int.ofNat 13, Int.ofNat 1, Int.negSucc 12, Int.negSucc 115, Int.ofNat 157, Int.negSucc 62, Int.ofNat 27, Int.ofNat 15, Int.negSucc 27, Int.negSucc 11, Int.negSucc 23, Int.ofNat 245, Int.negSucc 6, Int.ofNat 4, Int.negSucc 3, Int.ofNat 25, Int.negSucc 24, Int.negSucc 66, Int.ofNat 146, Int.ofNat 51, Int.ofNat 32],
  [Int.negSucc 3, Int.ofNat 5, Int.ofNat 2, Int.negSucc 64, Int.negSucc 52, Int.ofNat 29, Int.ofNat 1, Int.ofNat 5, Int.ofNat 4, Int.ofNat 28, Int.ofNat 16, Int.ofNat 1, Int.negSucc 4, Int.ofNat 7, Int.negSucc 0, Int.ofNat 4, Int.negSucc 36, Int.ofNat 79, Int.negSucc 46, Int.ofNat 28, Int.ofNat 31, Int.negSucc 59, Int.ofNat 1, Int.negSucc 25, Int.ofNat 372, Int.negSucc 9, Int.ofNat 4, Int.negSucc 6, Int.ofNat 29, Int.negSucc 24, Int.negSucc 66, Int.ofNat 154, Int.ofNat 53, Int.ofNat 31],
  [Int.negSucc 6, Int.ofNat 13, Int.ofNat 10, Int.negSucc 16, Int.negSucc 12, Int.ofNat 6, Int.ofNat 13, Int.ofNat 11, Int.negSucc 11, Int.ofNat 16, Int.ofNat 10, Int.negSucc 1, Int.ofNat 0, Int.negSucc 0, Int.ofNat 3, Int.ofNat 13, Int.ofNat 44, Int.negSucc 16, Int.negSucc 13, Int.ofNat 13, Int.ofNat 27, Int.negSucc 46, Int.ofNat 1, Int.negSucc 27, Int.ofNat 440, Int.negSucc 9, Int.ofNat 0, Int.negSucc 4, Int.ofNat 35, Int.negSucc 26, Int.negSucc 69, Int.ofNat 177, Int.ofNat 59, Int.ofNat 33],
  [Int.ofNat 0, Int.negSucc 1, Int.ofNat 2, Int.ofNat 27, Int.ofNat 20, Int.negSucc 8, Int.ofNat 0, Int.negSucc 2, Int.ofNat 3, Int.negSucc 6, Int.ofNat 4, Int.ofNat 4, Int.negSucc 1, Int.negSucc 1, Int.negSucc 2, Int.ofNat 21, Int.ofNat 98, Int.negSucc 105, Int.ofNat 40, Int.negSucc 10, Int.ofNat 12, Int.negSucc 28, Int.ofNat 4, Int.negSucc 31, Int.ofNat 493, Int.negSucc 14, Int.ofNat 3, Int.negSucc 7, Int.ofNat 42, Int.negSucc 29, Int.negSucc 73, Int.ofNat 196, Int.ofNat 64, Int.ofNat 35],
  [Int.ofNat 9, Int.negSucc 14, Int.negSucc 8, Int.ofNat 43, Int.ofNat 37, Int.negSucc 17, Int.negSucc 12, Int.negSucc 9, Int.ofNat 0, Int.negSucc 15, Int.ofNat 3, Int.ofNat 2, Int.ofNat 3, Int.negSucc 1, Int.negSucc 2, Int.ofNat 18, Int.ofNat 113, Int.negSucc 128, Int.ofNat 57, Int.negSucc 17, Int.ofNat 8, Int.negSucc 34, Int.ofNat 7, Int.negSucc 32, Int.ofNat 527, Int.negSucc 15, Int.ofNat 4, Int.negSucc 8, Int.ofNat 46, Int.negSucc 29, Int.negSucc 74, Int.ofNat 201, Int.ofNat 65, Int.ofNat 35]
]
private def V4bot : List (List Int) := V4bot_g0 ++ V4bot_g1 ++ V4bot_g2 ++ V4bot_g3 ++ V4bot_g4 ++ V4bot_g5 ++ V4bot_g6

private def Lam_g0 : List (List Int) := [
  [Int.negSucc 2962784, Int.negSucc 568427, Int.negSucc 66566, Int.ofNat 235725, Int.ofNat 306061, Int.ofNat 290289, Int.ofNat 228272, Int.ofNat 191541, Int.ofNat 134704, Int.ofNat 34314, Int.negSucc 32724, Int.ofNat 48353, Int.ofNat 207292, Int.ofNat 440722, Int.ofNat 64844, Int.ofNat 149396, Int.ofNat 183651, Int.ofNat 205249, Int.ofNat 198233, Int.ofNat 189884, Int.ofNat 190092, Int.ofNat 190092, Int.ofNat 189884, Int.ofNat 198233, Int.ofNat 205249, Int.ofNat 183651, Int.ofNat 149396, Int.ofNat 64844],
  [Int.negSucc 568427, Int.negSucc 835087, Int.negSucc 280294, Int.ofNat 9009, Int.ofNat 115652, Int.ofNat 120922, Int.ofNat 102895, Int.ofNat 105495, Int.ofNat 118843, Int.ofNat 62827, Int.ofNat 8418, Int.negSucc 17404, Int.ofNat 17733, Int.ofNat 207292, Int.ofNat 149396, Int.ofNat 47537, Int.ofNat 45009, Int.ofNat 65681, Int.ofNat 66414, Int.ofNat 80470, Int.ofNat 57997, Int.ofNat 57997, Int.ofNat 80470, Int.ofNat 66414, Int.ofNat 65681, Int.ofNat 45009, Int.ofNat 47537, Int.ofNat 149396],
  [Int.negSucc 66566, Int.negSucc 280294, Int.negSucc 1055580, Int.negSucc 255420, Int.ofNat 70415, Int.ofNat 124673, Int.ofNat 106215, Int.ofNat 118235, Int.ofNat 183181, Int.ofNat 185121, Int.ofNat 102784, Int.ofNat 13604, Int.negSucc 17404, Int.ofNat 48353, Int.ofNat 183651, Int.ofNat 45009, Int.ofNat 22678, Int.ofNat 36779, Int.ofNat 54219, Int.ofNat 48033, Int.ofNat 29648, Int.ofNat 29648, Int.ofNat 48033, Int.ofNat 54219, Int.ofNat 36779, Int.ofNat 22678, Int.ofNat 45009, Int.ofNat 183651],
  [Int.ofNat 235725, Int.ofNat 9009, Int.negSucc 255420, Int.negSucc 1548527, Int.negSucc 142442, Int.ofNat 144452, Int.ofNat 107001, Int.ofNat 106956, Int.ofNat 148193, Int.ofNat 305865, Int.ofNat 244085, Int.ofNat 102784, Int.ofNat 8418, Int.negSucc 32724, Int.ofNat 205249, Int.ofNat 65681, Int.ofNat 36779, Int.ofNat 26193, Int.ofNat 46326, Int.ofNat 7541, Int.negSucc 7630, Int.negSucc 7630, Int.ofNat 7541, Int.ofNat 46326, Int.ofNat 26193, Int.ofNat 36779, Int.ofNat 65681, Int.ofNat 205249],
  [Int.ofNat 306061, Int.ofNat 115652, Int.ofNat 70415, Int.negSucc 142442, Int.negSucc 1700582, Int.negSucc 104337, Int.ofNat 38626, Int.ofNat 85982, Int.ofNat 149126, Int.ofNat 201687, Int.ofNat 305865, Int.ofNat 185121, Int.ofNat 62827, Int.ofNat 34314, Int.ofNat 198233, Int.ofNat 66414, Int.ofNat 54219, Int.ofNat 46326, Int.ofNat 12906, Int.negSucc 11549, Int.negSucc 5378, Int.negSucc 5378, Int.negSucc 11549, Int.ofNat 12906, Int.ofNat 46326, Int.ofNat 54219, Int.ofNat 66414, Int.ofNat 198233],
  [Int.ofNat 290289, Int.ofNat 120922, Int.ofNat 124673, Int.ofNat 144452, Int.negSucc 104337, Int.negSucc 1615415, Int.negSucc 271068, Int.negSucc 20348, Int.ofNat 146136, Int.ofNat 149126, Int.ofNat 148193, Int.ofNat 183181, Int.ofNat 118843, Int.ofNat 134704, Int.ofNat 189884, Int.ofNat 80470, Int.ofNat 48033, Int.ofNat 7541, Int.negSucc 11549, Int.ofNat 21494, Int.ofNat 25777, Int.ofNat 25777, Int.ofNat 21494, Int.negSucc 11549, Int.ofNat 7541, Int.ofNat 48033, Int.ofNat 80470, Int.ofNat 189884],
  [Int.ofNat 228272, Int.ofNat 102895, Int.ofNat 106215, Int.ofNat 107001, Int.ofNat 38626, Int.negSucc 271068, Int.negSucc 1035355, Int.negSucc 277625, Int.negSucc 20348, Int.ofNat 85982, Int.ofNat 106956, Int.ofNat 118235, Int.ofNat 105495, Int.ofNat 191541, Int.ofNat 190092, Int.ofNat 57997, Int.ofNat 29648, Int.negSucc 7630, Int.negSucc 5378, Int.ofNat 25777, Int.ofNat 7838, Int.ofNat 7838, Int.ofNat 25777, Int.negSucc 5378, Int.negSucc 7630, Int.ofNat 29648, Int.ofNat 57997, Int.ofNat 190092]
]
private def Lam_g1 : List (List Int) := [
  [Int.ofNat 191541, Int.ofNat 105495, Int.ofNat 118235, Int.ofNat 106956, Int.ofNat 85982, Int.negSucc 20348, Int.negSucc 277625, Int.negSucc 1035355, Int.negSucc 271068, Int.ofNat 38626, Int.ofNat 107001, Int.ofNat 106215, Int.ofNat 102895, Int.ofNat 228272, Int.ofNat 190092, Int.ofNat 57997, Int.ofNat 29648, Int.negSucc 7630, Int.negSucc 5378, Int.ofNat 25777, Int.ofNat 7838, Int.ofNat 7838, Int.ofNat 25777, Int.negSucc 5378, Int.negSucc 7630, Int.ofNat 29648, Int.ofNat 57997, Int.ofNat 190092],
  [Int.ofNat 134704, Int.ofNat 118843, Int.ofNat 183181, Int.ofNat 148193, Int.ofNat 149126, Int.ofNat 146136, Int.negSucc 20348, Int.negSucc 271068, Int.negSucc 1615415, Int.negSucc 104337, Int.ofNat 144452, Int.ofNat 124673, Int.ofNat 120922, Int.ofNat 290289, Int.ofNat 189884, Int.ofNat 80470, Int.ofNat 48033, Int.ofNat 7541, Int.negSucc 11549, Int.ofNat 21494, Int.ofNat 25777, Int.ofNat 25777, Int.ofNat 21494, Int.negSucc 11549, Int.ofNat 7541, Int.ofNat 48033, Int.ofNat 80470, Int.ofNat 189884],
  [Int.ofNat 34314, Int.ofNat 62827, Int.ofNat 185121, Int.ofNat 305865, Int.ofNat 201687, Int.ofNat 149126, Int.ofNat 85982, Int.ofNat 38626, Int.negSucc 104337, Int.negSucc 1700582, Int.negSucc 142442, Int.ofNat 70415, Int.ofNat 115652, Int.ofNat 306061, Int.ofNat 198233, Int.ofNat 66414, Int.ofNat 54219, Int.ofNat 46326, Int.ofNat 12906, Int.negSucc 11549, Int.negSucc 5378, Int.negSucc 5378, Int.negSucc 11549, Int.ofNat 12906, Int.ofNat 46326, Int.ofNat 54219, Int.ofNat 66414, Int.ofNat 198233],
  [Int.negSucc 32724, Int.ofNat 8418, Int.ofNat 102784, Int.ofNat 244085, Int.ofNat 305865, Int.ofNat 148193, Int.ofNat 106956, Int.ofNat 107001, Int.ofNat 144452, Int.negSucc 142442, Int.negSucc 1548527, Int.negSucc 255420, Int.ofNat 9009, Int.ofNat 235725, Int.ofNat 205249, Int.ofNat 65681, Int.ofNat 36779, Int.ofNat 26193, Int.ofNat 46326, Int.ofNat 7541, Int.negSucc 7630, Int.negSucc 7630, Int.ofNat 7541, Int.ofNat 46326, Int.ofNat 26193, Int.ofNat 36779, Int.ofNat 65681, Int.ofNat 205249],
  [Int.ofNat 48353, Int.negSucc 17404, Int.ofNat 13604, Int.ofNat 102784, Int.ofNat 185121, Int.ofNat 183181, Int.ofNat 118235, Int.ofNat 106215, Int.ofNat 124673, Int.ofNat 70415, Int.negSucc 255420, Int.negSucc 1055580, Int.negSucc 280294, Int.negSucc 66566, Int.ofNat 183651, Int.ofNat 45009, Int.ofNat 22678, Int.ofNat 36779, Int.ofNat 54219, Int.ofNat 48033, Int.ofNat 29648, Int.ofNat 29648, Int.ofNat 48033, Int.ofNat 54219, Int.ofNat 36779, Int.ofNat 22678, Int.ofNat 45009, Int.ofNat 183651],
  [Int.ofNat 207292, Int.ofNat 17733, Int.negSucc 17404, Int.ofNat 8418, Int.ofNat 62827, Int.ofNat 118843, Int.ofNat 105495, Int.ofNat 102895, Int.ofNat 120922, Int.ofNat 115652, Int.ofNat 9009, Int.negSucc 280294, Int.negSucc 835087, Int.negSucc 568427, Int.ofNat 149396, Int.ofNat 47537, Int.ofNat 45009, Int.ofNat 65681, Int.ofNat 66414, Int.ofNat 80470, Int.ofNat 57997, Int.ofNat 57997, Int.ofNat 80470, Int.ofNat 66414, Int.ofNat 65681, Int.ofNat 45009, Int.ofNat 47537, Int.ofNat 149396],
  [Int.ofNat 440722, Int.ofNat 207292, Int.ofNat 48353, Int.negSucc 32724, Int.ofNat 34314, Int.ofNat 134704, Int.ofNat 191541, Int.ofNat 228272, Int.ofNat 290289, Int.ofNat 306061, Int.ofNat 235725, Int.negSucc 66566, Int.negSucc 568427, Int.negSucc 2962784, Int.ofNat 64844, Int.ofNat 149396, Int.ofNat 183651, Int.ofNat 205249, Int.ofNat 198233, Int.ofNat 189884, Int.ofNat 190092, Int.ofNat 190092, Int.ofNat 189884, Int.ofNat 198233, Int.ofNat 205249, Int.ofNat 183651, Int.ofNat 149396, Int.ofNat 64844]
]
private def Lam_g2 : List (List Int) := [
  [Int.ofNat 64844, Int.ofNat 149396, Int.ofNat 183651, Int.ofNat 205249, Int.ofNat 198233, Int.ofNat 189884, Int.ofNat 190092, Int.ofNat 190092, Int.ofNat 189884, Int.ofNat 198233, Int.ofNat 205249, Int.ofNat 183651, Int.ofNat 149396, Int.ofNat 64844, Int.negSucc 2962784, Int.negSucc 568427, Int.negSucc 66566, Int.ofNat 235725, Int.ofNat 306061, Int.ofNat 290289, Int.ofNat 228272, Int.ofNat 191541, Int.ofNat 134704, Int.ofNat 34314, Int.negSucc 32724, Int.ofNat 48353, Int.ofNat 207292, Int.ofNat 440722],
  [Int.ofNat 149396, Int.ofNat 47537, Int.ofNat 45009, Int.ofNat 65681, Int.ofNat 66414, Int.ofNat 80470, Int.ofNat 57997, Int.ofNat 57997, Int.ofNat 80470, Int.ofNat 66414, Int.ofNat 65681, Int.ofNat 45009, Int.ofNat 47537, Int.ofNat 149396, Int.negSucc 568427, Int.negSucc 835087, Int.negSucc 280294, Int.ofNat 9009, Int.ofNat 115652, Int.ofNat 120922, Int.ofNat 102895, Int.ofNat 105495, Int.ofNat 118843, Int.ofNat 62827, Int.ofNat 8418, Int.negSucc 17404, Int.ofNat 17733, Int.ofNat 207292],
  [Int.ofNat 183651, Int.ofNat 45009, Int.ofNat 22678, Int.ofNat 36779, Int.ofNat 54219, Int.ofNat 48033, Int.ofNat 29648, Int.ofNat 29648, Int.ofNat 48033, Int.ofNat 54219, Int.ofNat 36779, Int.ofNat 22678, Int.ofNat 45009, Int.ofNat 183651, Int.negSucc 66566, Int.negSucc 280294, Int.negSucc 1055580, Int.negSucc 255420, Int.ofNat 70415, Int.ofNat 124673, Int.ofNat 106215, Int.ofNat 118235, Int.ofNat 183181, Int.ofNat 185121, Int.ofNat 102784, Int.ofNat 13604, Int.negSucc 17404, Int.ofNat 48353],
  [Int.ofNat 205249, Int.ofNat 65681, Int.ofNat 36779, Int.ofNat 26193, Int.ofNat 46326, Int.ofNat 7541, Int.negSucc 7630, Int.negSucc 7630, Int.ofNat 7541, Int.ofNat 46326, Int.ofNat 26193, Int.ofNat 36779, Int.ofNat 65681, Int.ofNat 205249, Int.ofNat 235725, Int.ofNat 9009, Int.negSucc 255420, Int.negSucc 1548527, Int.negSucc 142442, Int.ofNat 144452, Int.ofNat 107001, Int.ofNat 106956, Int.ofNat 148193, Int.ofNat 305865, Int.ofNat 244085, Int.ofNat 102784, Int.ofNat 8418, Int.negSucc 32724],
  [Int.ofNat 198233, Int.ofNat 66414, Int.ofNat 54219, Int.ofNat 46326, Int.ofNat 12906, Int.negSucc 11549, Int.negSucc 5378, Int.negSucc 5378, Int.negSucc 11549, Int.ofNat 12906, Int.ofNat 46326, Int.ofNat 54219, Int.ofNat 66414, Int.ofNat 198233, Int.ofNat 306061, Int.ofNat 115652, Int.ofNat 70415, Int.negSucc 142442, Int.negSucc 1700582, Int.negSucc 104337, Int.ofNat 38626, Int.ofNat 85982, Int.ofNat 149126, Int.ofNat 201687, Int.ofNat 305865, Int.ofNat 185121, Int.ofNat 62827, Int.ofNat 34314],
  [Int.ofNat 189884, Int.ofNat 80470, Int.ofNat 48033, Int.ofNat 7541, Int.negSucc 11549, Int.ofNat 21494, Int.ofNat 25777, Int.ofNat 25777, Int.ofNat 21494, Int.negSucc 11549, Int.ofNat 7541, Int.ofNat 48033, Int.ofNat 80470, Int.ofNat 189884, Int.ofNat 290289, Int.ofNat 120922, Int.ofNat 124673, Int.ofNat 144452, Int.negSucc 104337, Int.negSucc 1615415, Int.negSucc 271068, Int.negSucc 20348, Int.ofNat 146136, Int.ofNat 149126, Int.ofNat 148193, Int.ofNat 183181, Int.ofNat 118843, Int.ofNat 134704],
  [Int.ofNat 190092, Int.ofNat 57997, Int.ofNat 29648, Int.negSucc 7630, Int.negSucc 5378, Int.ofNat 25777, Int.ofNat 7838, Int.ofNat 7838, Int.ofNat 25777, Int.negSucc 5378, Int.negSucc 7630, Int.ofNat 29648, Int.ofNat 57997, Int.ofNat 190092, Int.ofNat 228272, Int.ofNat 102895, Int.ofNat 106215, Int.ofNat 107001, Int.ofNat 38626, Int.negSucc 271068, Int.negSucc 1035355, Int.negSucc 277625, Int.negSucc 20348, Int.ofNat 85982, Int.ofNat 106956, Int.ofNat 118235, Int.ofNat 105495, Int.ofNat 191541]
]
private def Lam_g3 : List (List Int) := [
  [Int.ofNat 190092, Int.ofNat 57997, Int.ofNat 29648, Int.negSucc 7630, Int.negSucc 5378, Int.ofNat 25777, Int.ofNat 7838, Int.ofNat 7838, Int.ofNat 25777, Int.negSucc 5378, Int.negSucc 7630, Int.ofNat 29648, Int.ofNat 57997, Int.ofNat 190092, Int.ofNat 191541, Int.ofNat 105495, Int.ofNat 118235, Int.ofNat 106956, Int.ofNat 85982, Int.negSucc 20348, Int.negSucc 277625, Int.negSucc 1035355, Int.negSucc 271068, Int.ofNat 38626, Int.ofNat 107001, Int.ofNat 106215, Int.ofNat 102895, Int.ofNat 228272],
  [Int.ofNat 189884, Int.ofNat 80470, Int.ofNat 48033, Int.ofNat 7541, Int.negSucc 11549, Int.ofNat 21494, Int.ofNat 25777, Int.ofNat 25777, Int.ofNat 21494, Int.negSucc 11549, Int.ofNat 7541, Int.ofNat 48033, Int.ofNat 80470, Int.ofNat 189884, Int.ofNat 134704, Int.ofNat 118843, Int.ofNat 183181, Int.ofNat 148193, Int.ofNat 149126, Int.ofNat 146136, Int.negSucc 20348, Int.negSucc 271068, Int.negSucc 1615415, Int.negSucc 104337, Int.ofNat 144452, Int.ofNat 124673, Int.ofNat 120922, Int.ofNat 290289],
  [Int.ofNat 198233, Int.ofNat 66414, Int.ofNat 54219, Int.ofNat 46326, Int.ofNat 12906, Int.negSucc 11549, Int.negSucc 5378, Int.negSucc 5378, Int.negSucc 11549, Int.ofNat 12906, Int.ofNat 46326, Int.ofNat 54219, Int.ofNat 66414, Int.ofNat 198233, Int.ofNat 34314, Int.ofNat 62827, Int.ofNat 185121, Int.ofNat 305865, Int.ofNat 201687, Int.ofNat 149126, Int.ofNat 85982, Int.ofNat 38626, Int.negSucc 104337, Int.negSucc 1700582, Int.negSucc 142442, Int.ofNat 70415, Int.ofNat 115652, Int.ofNat 306061],
  [Int.ofNat 205249, Int.ofNat 65681, Int.ofNat 36779, Int.ofNat 26193, Int.ofNat 46326, Int.ofNat 7541, Int.negSucc 7630, Int.negSucc 7630, Int.ofNat 7541, Int.ofNat 46326, Int.ofNat 26193, Int.ofNat 36779, Int.ofNat 65681, Int.ofNat 205249, Int.negSucc 32724, Int.ofNat 8418, Int.ofNat 102784, Int.ofNat 244085, Int.ofNat 305865, Int.ofNat 148193, Int.ofNat 106956, Int.ofNat 107001, Int.ofNat 144452, Int.negSucc 142442, Int.negSucc 1548527, Int.negSucc 255420, Int.ofNat 9009, Int.ofNat 235725],
  [Int.ofNat 183651, Int.ofNat 45009, Int.ofNat 22678, Int.ofNat 36779, Int.ofNat 54219, Int.ofNat 48033, Int.ofNat 29648, Int.ofNat 29648, Int.ofNat 48033, Int.ofNat 54219, Int.ofNat 36779, Int.ofNat 22678, Int.ofNat 45009, Int.ofNat 183651, Int.ofNat 48353, Int.negSucc 17404, Int.ofNat 13604, Int.ofNat 102784, Int.ofNat 185121, Int.ofNat 183181, Int.ofNat 118235, Int.ofNat 106215, Int.ofNat 124673, Int.ofNat 70415, Int.negSucc 255420, Int.negSucc 1055580, Int.negSucc 280294, Int.negSucc 66566],
  [Int.ofNat 149396, Int.ofNat 47537, Int.ofNat 45009, Int.ofNat 65681, Int.ofNat 66414, Int.ofNat 80470, Int.ofNat 57997, Int.ofNat 57997, Int.ofNat 80470, Int.ofNat 66414, Int.ofNat 65681, Int.ofNat 45009, Int.ofNat 47537, Int.ofNat 149396, Int.ofNat 207292, Int.ofNat 17733, Int.negSucc 17404, Int.ofNat 8418, Int.ofNat 62827, Int.ofNat 118843, Int.ofNat 105495, Int.ofNat 102895, Int.ofNat 120922, Int.ofNat 115652, Int.ofNat 9009, Int.negSucc 280294, Int.negSucc 835087, Int.negSucc 568427],
  [Int.ofNat 64844, Int.ofNat 149396, Int.ofNat 183651, Int.ofNat 205249, Int.ofNat 198233, Int.ofNat 189884, Int.ofNat 190092, Int.ofNat 190092, Int.ofNat 189884, Int.ofNat 198233, Int.ofNat 205249, Int.ofNat 183651, Int.ofNat 149396, Int.ofNat 64844, Int.ofNat 440722, Int.ofNat 207292, Int.ofNat 48353, Int.negSucc 32724, Int.ofNat 34314, Int.ofNat 134704, Int.ofNat 191541, Int.ofNat 228272, Int.ofNat 290289, Int.ofNat 306061, Int.ofNat 235725, Int.negSucc 66566, Int.negSucc 568427, Int.negSucc 2962784]
]
private def Lambda28 : List (List Int) := Lam_g0 ++ Lam_g1 ++ Lam_g2 ++ Lam_g3
private def dotL (xs ys : List Int) (acc : Int := 0) : Int :=
  match xs, ys with
  | x :: xs, y :: ys => dotL xs ys (acc + x * y)
  | _, _ => acc

private structure RowData where
  idx : Nat
  r0 : List Int
  r1 : List Int
  r2 : List Int
  r3 : List Int
  r4t : List Int
  r4b : List Int


private def buildRowsGo (idx : Nat) (l0 l1 l2 l3 l4t l4b : List (List Int)) : List RowData :=
  match l0, l1, l2, l3, l4t, l4b with
  | a0 :: t0, a1 :: t1, a2 :: t2, a3 :: t3, a4t :: t4t, a4b :: t4b =>
    { idx := idx, r0 := a0, r1 := a1, r2 := a2, r3 := a3, r4t := a4t, r4b := a4b } ::
    buildRowsGo (idx + 1) t0 t1 t2 t3 t4t t4b
  | _, _, _, _, _, _ => []

private def buildRows : List RowData :=
  buildRowsGo 0 V0 V1 V2 V3 V4top V4bot

private def allRows : List RowData := buildRows

private def checkPair (a b : RowData) : Bool :=
  let ri := a.idx / 7
  let rj := a.idx % 7
  let ci := b.idx / 7
  let cj := b.idx % 7
  let g0 := dotL a.r0 b.r0
  let g1 := dotL a.r1 b.r1
  let g2 := dotL a.r2 b.r2
  let g3 := dotL a.r3 b.r3
  let g400 := dotL a.r4t b.r4t
  let g401 := dotL a.r4t b.r4b
  let g410 := dotL a.r4b b.r4t
  let g411 := dotL a.r4b b.r4b
  let ciNeg := 13 - ci
  let cjNeg := 13 - cj
  let lamRow := match Lambda28.drop ri with | r :: _ => r | [] => []
  let lP_pos := getAt lamRow ci
  let lP_neg := getAt lamRow ciNeg
  let lQ_pos := getAt lamRow (14 + ci)
  let lQ_neg := getAt lamRow (14 + ciNeg)
  let sPpp := (g0 + g1) + (g2 + g3) + g400 + g411
  let sPpm := (g0 + g1) - (g2 + g3) - g400 + g411
  let sPmp := (g0 + g1) - (g2 + g3) + g400 - g411
  let sPmm := (g0 + g1) + (g2 + g3) - g400 - g411
  let sQpp := (g0 - g1) + (g2 - g3) + g401 + g410
  let sQpm := (g0 - g1) - (g2 - g3) + g401 - g410
  let sQmp := (g0 - g1) - (g2 - g3) - g401 + g410
  let sQmm := (g0 - g1) + (g2 - g3) - g401 - g410
  (M1Int ri rj ci cj - sPpp ≥ lP_pos) &&
  (M1Int ri rj ci cjNeg - sPpm ≥ lP_pos) &&
  (M1Int ri rj ciNeg cj - sPmp ≥ lP_neg) &&
  (M1Int ri rj ciNeg cjNeg - sPmm ≥ lP_neg) &&
  (M12Int ri rj ci cj - sQpp ≥ lQ_pos) &&
  (M12Int ri rj ci cjNeg - sQpm ≥ lQ_pos) &&
  (M12Int ri rj ciNeg cj - sQmp ≥ lQ_neg) &&
  (M12Int ri rj ciNeg cjNeg - sQmm ≥ lQ_neg)

private def checkSlice (start len : Nat) : Bool :=
  (allRows.drop start |>.take len).all fun a => allRows.all fun b => checkPair a b

private def sumRows (rs : List (List Int)) : Int :=
  match rs with
  | [] => 0
  | r :: rest => (r.foldl (· + ·) 0) + sumRows rest

-- ============================================================================
-- Section 6B: D4 SOS dual certificate, invariance, and final theorem
-- ============================================================================

private lemma sum_ok : sumRows Lam_g0 + sumRows Lam_g1 + sumRows Lam_g2 + sumRows Lam_g3 = 8560536 := by decide
private lemma chunk0 : checkSlice 0 7 = true := by decide
private lemma chunk1 : checkSlice 7 7 = true := by decide
private lemma chunk2 : checkSlice 14 7 = true := by decide
private lemma chunk3 : checkSlice 21 7 = true := by decide
private lemma chunk4 : checkSlice 28 7 = true := by decide
private lemma chunk5 : checkSlice 35 7 = true := by decide
private lemma chunk6 : checkSlice 42 7 = true := by decide

private def rowAt (M : List (List ℤ)) (r : ℕ) : List ℤ :=
  match M.drop r with
  | row :: _ => row
  | [] => []

private def matAt (M : List (List ℤ)) (r c : ℕ) : ℤ :=
  getAt (rowAt M r) c

private def rev14 (i : Fin 14) : Fin 14 := ⟨13 - i.1, by omega⟩
private def idx7 (i : Fin 14) : ℕ := if i.1 < 7 then i.1 else 13 - i.1
private def sgn7 (i : Fin 14) : ℤ := if i.1 < 7 then 1 else -1
private def idx49 (i j : Fin 14) : ℕ := idx7 i * 7 + idx7 j
private def sgnP (p : Bool) : ℤ := if p = false then 1 else -1

private def lamAt28 (p : Bool) (i : Fin 14) (q : Bool) (l : Fin 14) : ℤ :=
  matAt Lambda28 ((if p then 14 else 0) + i.1) ((if q then 14 else 0) + l.1)

private lemma V0_len : V0.length = 49 := by decide
private lemma V1_len : V1.length = 49 := by decide
private lemma V2_len : V2.length = 49 := by decide
private lemma V3_len : V3.length = 49 := by decide
private lemma V4top_len : V4top.length = 49 := by decide
private lemma V4bot_len : V4bot.length = 49 := by decide
private lemma V0_cols : V0.all (fun r => r.length == 17) = true := by decide
private lemma V1_cols : V1.all (fun r => r.length == 18) = true := by decide
private lemma V2_cols : V2.all (fun r => r.length == 16) = true := by decide
private lemma V3_cols : V3.all (fun r => r.length == 17) = true := by decide
private lemma V4top_cols : V4top.all (fun r => r.length == 34) = true := by decide
private lemma V4bot_cols : V4bot.all (fun r => r.length == 34) = true := by decide
private lemma Lam28_len : Lambda28.length = 28 := by decide
private lemma Lam28_cols : Lambda28.all (fun r => r.length == 28) = true := by decide

private lemma wxList_rev (i : Fin 14) : getAt wxList (13 - i.1) = getAt wxList i.1 := by
  fin_cases i <;> decide

private lemma exLoList_rev (i : Fin 15) : getAt exLoList (14 - i.1) = 10000 - getAt exHiList i.1 := by
  fin_cases i <;> decide

private lemma exHiList_rev (i : Fin 15) : getAt exHiList (14 - i.1) = 10000 - getAt exLoList i.1 := by
  fin_cases i <;> decide

private lemma eyList_rev (i : Fin 15) : getAt eyList (14 - i.1) = 10000 - getAt eyList i.1 := by
  fin_cases i <;> decide

private lemma ex_ordered (i : Fin 14) : getAt exLoList i.1 ≤ getAt exHiList (i.1 + 1) := by
  fin_cases i <;> decide

private lemma lamAt28_swap (p q : Bool) (i l : Fin 14) :
    lamAt28 (!p) i (!q) l = lamAt28 p i q l := by
  revert p q i l; decide

private lemma lamAt28_flipX (p q : Bool) (i l : Fin 14) :
    lamAt28 p (if p = false then rev14 i else i) q (if q = false then rev14 l else l) = lamAt28 p i q l := by
  revert p q i l; decide

private lemma lamAt28_flipY (p q : Bool) (i l : Fin 14) :
    lamAt28 p (if p = true then rev14 i else i) q (if q = true then rev14 l else l) = lamAt28 p i q l := by
  revert p q i l; decide

private lemma idx7_lt (i : Fin 14) : idx7 i < 7 := by
  unfold idx7; split_ifs <;> omega

private lemma idx49_lt (i j : Fin 14) : idx49 i j < 49 := by
  unfold idx49; have := idx7_lt i; have := idx7_lt j; omega

private lemma idx7_rev (i : Fin 14) : idx7 (rev14 i) = idx7 i := by
  unfold idx7 rev14; dsimp only; split_ifs <;> omega

private lemma sgn7_rev (i : Fin 14) : sgn7 (rev14 i) = -sgn7 i := by
  unfold sgn7 rev14; dsimp only; split_ifs <;> omega

private lemma sgnP_not (p : Bool) : sgnP (!p) = -sgnP p := by
  cases p <;> rfl

private lemma rowAt_succ (r : ℕ) (x : List ℤ) (xs : List (List ℤ)) :
    rowAt (x :: xs) (r + 1) = rowAt xs r := by
  simp [rowAt, List.drop_succ_cons]

private lemma rowAt_length {M : List (List ℤ)} {d r : ℕ}
    (hall : M.all (fun row => row.length == d) = true) (hr : r < M.length) :
    (rowAt M r).length = d := by
  induction M generalizing r with
  | nil => simp at hr
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
    cases r with
    | zero => simpa [rowAt] using hall.1
    | succ k =>
      rw [rowAt_succ]
      exact ih hall.2 (Nat.lt_of_succ_lt_succ hr)

private lemma dotL_eq_sum_acc : ∀ (n : ℕ) (xs ys : List ℤ),
    xs.length = n → ys.length = n → ∀ (acc : ℤ),
    dotL xs ys acc = acc + ∑ k : Fin n, getAt xs k.1 * getAt ys k.1 := by
  intro n
  induction n with
  | zero =>
    intro xs ys hxs hys acc
    cases xs <;> cases ys <;> simp [dotL] at hxs hys ⊢
  | succ m ih =>
    intro xs ys hxs hys acc
    rcases xs with _ | ⟨x, xt⟩ <;> rcases ys with _ | ⟨y, yt⟩
    · simp at hxs
    · simp at hxs
    · simp at hys
    · simp only [List.length_cons, Nat.succ.injEq] at hxs hys
      rw [dotL, ih xt yt hxs hys (acc + x * y), Fin.sum_univ_succ]
      simp [getAt, Fin.val_succ]
      ring

private lemma dotL_eq_sum {n : ℕ} {xs ys : List ℤ} (hxs : xs.length = n) (hys : ys.length = n) :
    dotL xs ys 0 = ∑ k : Fin n, getAt xs k.1 * getAt ys k.1 := by
  rw [dotL_eq_sum_acc n xs ys hxs hys 0, zero_add]

private lemma list_take_add {α : Type*} : ∀ (L : List α) (a b : ℕ),
    L.take (a + b) = L.take a ++ (L.drop a).take b := by
  intro L a
  induction a generalizing L with
  | zero => intro b; simp
  | succ k ih =>
    intro b
    cases L with
    | nil => simp
    | cons x t =>
      rw [Nat.succ_add, List.take_succ_cons, List.take_succ_cons, List.drop_succ_cons, ih t b,
        List.cons_append]

private lemma list_all_iff_take7 {α : Type*} {L : List α} {P : α → Bool} (hlen : L.length = 49)
    (h0 : ((L.drop 0).take 7).all P = true)
    (h1 : ((L.drop 7).take 7).all P = true)
    (h2 : ((L.drop 14).take 7).all P = true)
    (h3 : ((L.drop 21).take 7).all P = true)
    (h4 : ((L.drop 28).take 7).all P = true)
    (h5 : ((L.drop 35).take 7).all P = true)
    (h6 : ((L.drop 42).take 7).all P = true) :
    L.all P = true := by
  have ht7 : (L.take 7).all P = true := by simpa using h0
  have ht14 : (L.take 14).all P = true := by
    rw [show (14 : ℕ) = 7 + 7 by rfl, list_take_add, List.all_append, ht7, h1]; rfl
  have ht21 : (L.take 21).all P = true := by
    rw [show (21 : ℕ) = 14 + 7 by rfl, list_take_add, List.all_append, ht14, h2]; rfl
  have ht28 : (L.take 28).all P = true := by
    rw [show (28 : ℕ) = 21 + 7 by rfl, list_take_add, List.all_append, ht21, h3]; rfl
  have ht35 : (L.take 35).all P = true := by
    rw [show (35 : ℕ) = 28 + 7 by rfl, list_take_add, List.all_append, ht28, h4]; rfl
  have ht42 : (L.take 42).all P = true := by
    rw [show (42 : ℕ) = 35 + 7 by rfl, list_take_add, List.all_append, ht35, h5]; rfl
  have ht49 : (L.take 49).all P = true := by
    rw [show (49 : ℕ) = 42 + 7 by rfl, list_take_add, List.all_append, ht42, h6]; rfl
  rwa [← hlen, List.take_length] at ht49

private lemma buildRowsGo_length : ∀ (m idx : ℕ) (l0 l1 l2 l3 l4t l4b : List (List ℤ)),
    l0.length = m → l1.length = m → l2.length = m →
    l3.length = m → l4t.length = m → l4b.length = m →
    (buildRowsGo idx l0 l1 l2 l3 l4t l4b).length = m := by
  intro m
  induction m with
  | zero =>
    intro idx l0 l1 l2 l3 l4t l4b h0 _ _ _ _ _
    cases l0 <;> simp at h0 ⊢
    simp [buildRowsGo]
  | succ m' ih =>
    intro idx l0 l1 l2 l3 l4t l4b h0 h1 h2 h3 h4t h4b
    rcases l0 with _ | ⟨a0, t0⟩; · simp at h0
    rcases l1 with _ | ⟨a1, t1⟩; · simp at h1
    rcases l2 with _ | ⟨a2, t2⟩; · simp at h2
    rcases l3 with _ | ⟨a3, t3⟩; · simp at h3
    rcases l4t with _ | ⟨a4t, t4t⟩; · simp at h4t
    rcases l4b with _ | ⟨a4b, t4b⟩; · simp at h4b
    simp only [List.length_cons, Nat.succ.injEq] at h0 h1 h2 h3 h4t h4b
    simp only [buildRowsGo, List.length_cons]
    rw [ih (idx + 1) t0 t1 t2 t3 t4t t4b h0 h1 h2 h3 h4t h4b]

private lemma buildRowsGo_get : ∀ (m idx : ℕ) (l0 l1 l2 l3 l4t l4b : List (List ℤ)) (k : ℕ)
    (h0 : l0.length = m) (h1 : l1.length = m) (h2 : l2.length = m)
    (h3 : l3.length = m) (h4t : l4t.length = m) (h4b : l4b.length = m)
    (hk : k < m),
    (buildRowsGo idx l0 l1 l2 l3 l4t l4b)[k]'(by
      rw [buildRowsGo_length m idx l0 l1 l2 l3 l4t l4b h0 h1 h2 h3 h4t h4b]; exact hk) =
      { idx := idx + k, r0 := rowAt l0 k, r1 := rowAt l1 k, r2 := rowAt l2 k,
        r3 := rowAt l3 k, r4t := rowAt l4t k, r4b := rowAt l4b k } := by
  intro m
  induction m with
  | zero => intro _ _ _ _ _ _ _ k _ _ _ _ _ _ hk; omega
  | succ m' ih =>
    intro idx l0 l1 l2 l3 l4t l4b k h0 h1 h2 h3 h4t h4b hk
    rcases l0 with _ | ⟨a0, t0⟩; · simp at h0
    rcases l1 with _ | ⟨a1, t1⟩; · simp at h1
    rcases l2 with _ | ⟨a2, t2⟩; · simp at h2
    rcases l3 with _ | ⟨a3, t3⟩; · simp at h3
    rcases l4t with _ | ⟨a4t, t4t⟩; · simp at h4t
    rcases l4b with _ | ⟨a4b, t4b⟩; · simp at h4b
    simp only [List.length_cons, Nat.succ.injEq] at h0 h1 h2 h3 h4t h4b
    cases k with
    | zero => simp [buildRowsGo, rowAt]
    | succ k' =>
      have heq := ih (idx + 1) t0 t1 t2 t3 t4t t4b k' h0 h1 h2 h3 h4t h4b (Nat.lt_of_succ_lt_succ hk)
      simp only [buildRowsGo, List.getElem_cons_succ, heq]
      congr 1
      omega

private lemma allRows_length : allRows.length = 49 := by
  exact buildRowsGo_length 49 0 V0 V1 V2 V3 V4top V4bot V0_len V1_len V2_len V3_len V4top_len V4bot_len

private lemma allRows_get (r : Fin 49) :
    allRows[r.1]'(by rw [allRows_length]; exact r.2) =
      { idx := r.1, r0 := rowAt V0 r.1, r1 := rowAt V1 r.1, r2 := rowAt V2 r.1,
        r3 := rowAt V3 r.1, r4t := rowAt V4top r.1, r4b := rowAt V4bot r.1 } := by
  have heq := buildRowsGo_get 49 0 V0 V1 V2 V3 V4top V4bot r.1 V0_len V1_len V2_len V3_len V4top_len V4bot_len r.2
  simpa [allRows, buildRows] using heq

private lemma checkPair_all (r c : Fin 49) :
    checkPair
      { idx := r.1, r0 := rowAt V0 r.1, r1 := rowAt V1 r.1, r2 := rowAt V2 r.1,
        r3 := rowAt V3 r.1, r4t := rowAt V4top r.1, r4b := rowAt V4bot r.1 }
      { idx := c.1, r0 := rowAt V0 c.1, r1 := rowAt V1 c.1, r2 := rowAt V2 c.1,
        r3 := rowAt V3 c.1, r4t := rowAt V4top c.1, r4b := rowAt V4bot c.1 } = true := by
  have hall : allRows.all (fun a => allRows.all fun b => checkPair a b) = true :=
    list_all_iff_take7 allRows_length chunk0 chunk1 chunk2 chunk3 chunk4 chunk5 chunk6
  have ha := List.all_eq_true.mp hall (allRows[r.1]'(by rw [allRows_length]; exact r.2))
    (List.getElem_mem _)
  have hb := List.all_eq_true.mp ha (allRows[c.1]'(by rw [allRows_length]; exact c.2))
    (List.getElem_mem _)
  rw [allRows_get r, allRows_get c] at hb
  exact hb

private lemma sumRows_append (xs ys : List (List ℤ)) :
    sumRows (xs ++ ys) = sumRows xs + sumRows ys := by
  induction xs with
  | nil => simp [sumRows]
  | cons a t ih => simp [sumRows, ih]; ring

private lemma foldl_add_eq_sum : ∀ (row : List ℤ) (acc : ℤ),
    row.foldl (· + ·) acc = acc + ∑ c : Fin row.length, getAt row c.1 := by
  intro row
  induction row with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    dsimp only [List.length_cons]
    rw [List.foldl_cons, ih (acc + x), Fin.sum_univ_succ]
    simp [getAt, Fin.val_succ]
    ring

private lemma sum_fin_congr {m n : ℕ} (h : m = n) (f : ℕ → ℤ) :
    (∑ i : Fin m, f i.1) = ∑ i : Fin n, f i.1 := by
  subst h; rfl

private lemma sumRows_eq_sum (rs : List (List ℤ)) (d : ℕ)
    (hd : rs.all (fun row => row.length == d) = true) :
    sumRows rs = ∑ r : Fin rs.length, ∑ c : Fin d, matAt rs r.1 c.1 := by
  induction rs with
  | nil => simp [sumRows]
  | cons row rest ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hd
    dsimp only [List.length_cons]
    rw [sumRows, foldl_add_eq_sum, zero_add, ih hd.2, Fin.sum_univ_succ]
    congr 1
    exact sum_fin_congr hd.1 (fun c => getAt row c)

private lemma sum_lamAt28 :
    ∑ p : Bool, ∑ i : Fin 14, ∑ q : Bool, ∑ l : Fin 14, lamAt28 p i q l = 8560536 := by
  have hL : sumRows Lambda28 = 8560536 := by
    have h1 : Lambda28 = Lam_g0 ++ Lam_g1 ++ Lam_g2 ++ Lam_g3 := rfl
    rw [h1, sumRows_append, sumRows_append, sumRows_append]
    linarith [sum_ok]
  have hsum : sumRows Lambda28 = ∑ r : Fin 28, ∑ c : Fin 28, matAt Lambda28 r.1 c.1 := by
    rw [sumRows_eq_sum Lambda28 28 Lam28_cols]
    exact sum_fin_congr Lam28_len (fun r => ∑ c : Fin 28, matAt Lambda28 r c.1)
  have hsplit_28 : ∀ f : ℕ → ℤ,
      (∑ r : Fin 28, f r.1) = ∑ p : Bool, ∑ i : Fin 14, f ((if p then 14 else 0) + i.1) := fun f => by
    have h28 : (∑ r : Fin (14 + 14), f r.1) = (∑ i : Fin 14, f i.1) + ∑ i : Fin 14, f (14 + i.1) := by
      rw [Fin.sum_univ_add]
      simp [Fin.val_castAdd]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.add_comm]
    rw [show (28 : ℕ) = 14 + 14 by rfl, h28, Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
    ring
  rw [← hL, hsum, hsplit_28 (fun r => ∑ c : Fin 28, matAt Lambda28 r c.1)]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => ?_
  exact (hsplit_28 (fun c => matAt Lambda28 ((if p then 14 else 0) + i.1) c)).symm

private def vec0 (k : Fin 17) : Idx → ℤ | (_, i, j) => matAt V0 (idx49 i j) k.1
private def vec1 (k : Fin 18) : Idx → ℤ | (p, i, j) => sgnP p * matAt V1 (idx49 i j) k.1
private def vec2 (k : Fin 16) : Idx → ℤ | (_, i, j) => sgn7 i * sgn7 j * matAt V2 (idx49 i j) k.1
private def vec3 (k : Fin 17) : Idx → ℤ | (p, i, j) => sgnP p * sgn7 i * sgn7 j * matAt V3 (idx49 i j) k.1
private def vec4a (k : Fin 34) : Idx → ℤ
  | (p, i, j) => if p = false then sgn7 j * matAt V4top (idx49 i j) k.1 else sgn7 i * matAt V4bot (idx49 i j) k.1
private def vec4b (k : Fin 34) : Idx → ℤ
  | (p, i, j) => if p = false then sgn7 i * matAt V4bot (idx49 i j) k.1 else sgn7 j * matAt V4top (idx49 i j) k.1

private def S_int (a b : Idx) : ℤ :=
  (∑ k : Fin 17, vec0 k a * vec0 k b) +
  (∑ k : Fin 18, vec1 k a * vec1 k b) +
  (∑ k : Fin 16, vec2 k a * vec2 k b) +
  (∑ k : Fin 17, vec3 k a * vec3 k b) +
  (∑ k : Fin 34, vec4a k a * vec4a k b) +
  (∑ k : Fin 34, vec4b k a * vec4b k b)

private lemma quad_outer_nonneg {m : ℕ} (v : Fin m → Idx → ℤ) (z : Idx → ℝ) :
    0 ≤ ∑ a : Idx, ∑ b : Idx, z a * z b * ((∑ k : Fin m, v k a * v k b : ℤ) : ℝ) := by
  have h1 : (∑ a : Idx, ∑ b : Idx, z a * z b * ((∑ k : Fin m, v k a * v k b : ℤ) : ℝ)) =
      ∑ k : Fin m, (∑ a : Idx, z a * (v k a : ℝ)) ^ 2 := by
    push_cast
    simp_rw [Finset.mul_sum]
    have h2 : ∑ a : Idx, ∑ b : Idx, ∑ k : Fin m, z a * z b * ((v k a : ℝ) * v k b) =
        ∑ k : Fin m, ∑ a : Idx, ∑ b : Idx, (z a * (v k a : ℝ)) * (z b * (v k b : ℝ)) := by
      calc ∑ a : Idx, ∑ b : Idx, ∑ k : Fin m, z a * z b * ((v k a : ℝ) * v k b)
          = ∑ a : Idx, ∑ k : Fin m, ∑ b : Idx, z a * z b * ((v k a : ℝ) * v k b) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ k : Fin m, ∑ a : Idx, ∑ b : Idx, z a * z b * ((v k a : ℝ) * v k b) := Finset.sum_comm
        _ = ∑ k : Fin m, ∑ a : Idx, ∑ b : Idx, (z a * (v k a : ℝ)) * (z b * (v k b : ℝ)) := by
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
              Finset.sum_congr rfl fun b _ => by ring
    rw [h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sq, Fintype.sum_mul_sum]
  rw [h1]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

private lemma S_int_psd (z : Idx → ℝ) :
    0 ≤ ∑ a : Idx, ∑ b : Idx, z a * z b * (S_int a b : ℝ) := by
  have hsplit : (∑ a : Idx, ∑ b : Idx, z a * z b * (S_int a b : ℝ)) =
      (∑ a : Idx, ∑ b : Idx, z a * z b * ((∑ k : Fin 17, vec0 k a * vec0 k b : ℤ) : ℝ)) +
      (∑ a : Idx, ∑ b : Idx, z a * z b * ((∑ k : Fin 18, vec1 k a * vec1 k b : ℤ) : ℝ)) +
      (∑ a : Idx, ∑ b : Idx, z a * z b * ((∑ k : Fin 16, vec2 k a * vec2 k b : ℤ) : ℝ)) +
      (∑ a : Idx, ∑ b : Idx, z a * z b * ((∑ k : Fin 17, vec3 k a * vec3 k b : ℤ) : ℝ)) +
      (∑ a : Idx, ∑ b : Idx, z a * z b * ((∑ k : Fin 34, vec4a k a * vec4a k b : ℤ) : ℝ)) +
      (∑ a : Idx, ∑ b : Idx, z a * z b * ((∑ k : Fin 34, vec4b k a * vec4b k b : ℤ) : ℝ)) := by
    simp only [S_int, Int.cast_add, mul_add, Finset.sum_add_distrib]
  rw [hsplit]
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (quad_outer_nonneg vec0 z) (quad_outer_nonneg vec1 z))
    (quad_outer_nonneg vec2 z)) (quad_outer_nonneg vec3 z))
    (quad_outer_nonneg vec4a z)) (quad_outer_nonneg vec4b z)

private def gSwap : Idx → Idx
  | (p, i, j) => (!p, i, j)

private def gFlipX : Idx → Idx
  | (false, i, j) => (false, rev14 i, j)
  | (true, i, j) => (true, i, rev14 j)

private def gFlipY : Idx → Idx
  | (false, i, j) => (false, i, rev14 j)
  | (true, i, j) => (true, rev14 i, j)

private lemma gFlipY_eq (a : Idx) : gFlipY a = gSwap (gFlipX (gSwap a)) := by
  rcases a with ⟨p, i, j⟩; cases p <;> rfl

private lemma S_int_gSwap (a b : Idx) : S_int (gSwap a) (gSwap b) = S_int a b := by
  rcases a with ⟨p, i, j⟩; rcases b with ⟨q, l, k⟩
  simp only [S_int, gSwap, vec0, vec1, vec2, vec3, vec4a, vec4b, sgnP_not]
  have h1 : ∀ (x y : ℤ), (-x) * (-y) = x * y := fun _ _ => by ring
  have h1s : ∑ x : Fin 18, (-sgnP p * matAt V1 (idx49 i j) x.1) * (-sgnP q * matAt V1 (idx49 l k) x.1) =
      ∑ x : Fin 18, (sgnP p * matAt V1 (idx49 i j) x.1) * (sgnP q * matAt V1 (idx49 l k) x.1) := by
    refine Finset.sum_congr rfl fun _ _ => by ring
  have h3s : ∑ x : Fin 17, (-sgnP p * sgn7 i * sgn7 j * matAt V3 (idx49 i j) x.1) *
      (-sgnP q * sgn7 l * sgn7 k * matAt V3 (idx49 l k) x.1) =
      ∑ x : Fin 17, (sgnP p * sgn7 i * sgn7 j * matAt V3 (idx49 i j) x.1) *
      (sgnP q * sgn7 l * sgn7 k * matAt V3 (idx49 l k) x.1) := by
    refine Finset.sum_congr rfl fun _ _ => by ring
  rw [h1s, h3s]
  cases p <;> cases q <;> simp <;> ring

private lemma S_int_gFlipX (a b : Idx) : S_int (gFlipX a) (gFlipX b) = S_int a b := by
  rcases a with ⟨p, i, j⟩; rcases b with ⟨q, l, k⟩
  have hfx_0 : ∀ (x : Fin 17) (a' : Idx), vec0 x (gFlipX a') = vec0 x a' := fun x ⟨p', i', j'⟩ => by
    cases p' <;> simp [gFlipX, vec0, idx49, idx7_rev]
  have hfx_1 : ∀ (x : Fin 18) (a' : Idx), vec1 x (gFlipX a') = vec1 x a' := fun x ⟨p', i', j'⟩ => by
    cases p' <;> simp [gFlipX, vec1, idx49, idx7_rev]
  have hfx_2 : ∀ (x : Fin 16) (a' : Idx), vec2 x (gFlipX a') = -vec2 x a' := fun x ⟨p', i', j'⟩ => by
    cases p' <;> simp [gFlipX, vec2, idx49, idx7_rev, sgn7_rev]
  have hfx_3 : ∀ (x : Fin 17) (a' : Idx), vec3 x (gFlipX a') = -vec3 x a' := fun x ⟨p', i', j'⟩ => by
    cases p' <;> simp [gFlipX, vec3, idx49, idx7_rev, sgn7_rev]
  have hfx_4a : ∀ (x : Fin 34) (a' : Idx), vec4a x (gFlipX a') = vec4a x a' := fun x ⟨p', i', j'⟩ => by
    cases p' <;> simp [gFlipX, vec4a, idx49, idx7_rev]
  have hfx_4b : ∀ (x : Fin 34) (a' : Idx), vec4b x (gFlipX a') = -vec4b x a' := fun x ⟨p', i', j'⟩ => by
    cases p' <;> simp [gFlipX, vec4b, idx49, idx7_rev, sgn7_rev]
  simp only [S_int, hfx_0, hfx_1, hfx_2, hfx_3, hfx_4a, hfx_4b, neg_mul_neg]

private lemma S_int_gFlipY (a b : Idx) : S_int (gFlipY a) (gFlipY b) = S_int a b := by
  rw [gFlipY_eq a, gFlipY_eq b, S_int_gSwap, S_int_gFlipX, S_int_gSwap]

private lemma distIv_comm {alo ahi blo bhi : ℤ} (ha : alo ≤ ahi) (hb : blo ≤ bhi) :
    distIv alo ahi blo bhi = distIv blo bhi alo ahi := by
  unfold distIv; split_ifs <;> omega

private lemma maxdistIv_comm (alo ahi blo bhi : ℤ) :
    maxdistIv blo bhi alo ahi = maxdistIv alo ahi blo bhi := by
  unfold maxdistIv
  dsimp only
  have h1 : Int.natAbs (blo - ahi) = Int.natAbs (ahi - blo) := by omega
  have h2 : Int.natAbs (bhi - alo) = Int.natAbs (alo - bhi) := by omega
  rw [h1, h2, apply_ite Int.ofNat, apply_ite Int.ofNat]
  simp only [Int.ofNat_eq_natCast]
  split_ifs <;> omega

private lemma distIv_reflect (C : ℤ) {alo ahi blo bhi : ℤ} (ha : alo ≤ ahi) (hb : blo ≤ bhi) :
    distIv (C - ahi) (C - alo) (C - bhi) (C - blo) = distIv alo ahi blo bhi := by
  unfold distIv; split_ifs <;> omega

private lemma maxdistIv_reflect (C alo ahi blo bhi : ℤ) :
    maxdistIv (C - ahi) (C - alo) (C - bhi) (C - blo) = maxdistIv alo ahi blo bhi := by
  unfold maxdistIv
  dsimp only
  have h1 : Int.natAbs ((C - ahi) - (C - blo)) = Int.natAbs (ahi - blo) := by omega
  have h2 : Int.natAbs ((C - alo) - (C - bhi)) = Int.natAbs (alo - bhi) := by omega
  rw [h1, h2, apply_ite Int.ofNat, apply_ite Int.ofNat]
  simp only [Int.ofNat_eq_natCast]
  split_ifs <;> omega

private lemma distIv_le_maxdistIv {alo ahi blo bhi : ℤ} (ha : alo ≤ ahi) (hb : blo ≤ bhi) :
    distIv alo ahi blo bhi ≤ maxdistIv alo ahi blo bhi := by
  unfold distIv maxdistIv
  dsimp only
  rw [apply_ite Int.ofNat]
  simp only [Int.ofNat_eq_natCast]
  split_ifs <;> omega

private lemma M12Int_swap (i j l k : Fin 14) :
    M12Int l.1 k.1 i.1 j.1 = M12Int i.1 j.1 l.1 k.1 := by
  unfold M12Int
  dsimp only
  have h1 : distIv (getAt exLoList l.1) (getAt exHiList (l.1 + 1)) (getAt eyList j.1) (getAt eyList (j.1 + 1)) =
      distIv (getAt eyList j.1) (getAt eyList (j.1 + 1)) (getAt exLoList l.1) (getAt exHiList (l.1 + 1)) :=
    distIv_comm (ex_ordered l) (eyList_mono j)
  have h2 : maxdistIv (getAt exLoList l.1) (getAt exHiList (l.1 + 1)) (getAt eyList j.1) (getAt eyList (j.1 + 1)) =
      maxdistIv (getAt eyList j.1) (getAt eyList (j.1 + 1)) (getAt exLoList l.1) (getAt exHiList (l.1 + 1)) :=
    maxdistIv_comm _ _ _ _
  have h3 : distIv (getAt eyList k.1) (getAt eyList (k.1 + 1)) (getAt exLoList i.1) (getAt exHiList (i.1 + 1)) =
      distIv (getAt exLoList i.1) (getAt exHiList (i.1 + 1)) (getAt eyList k.1) (getAt eyList (k.1 + 1)) :=
    distIv_comm (eyList_mono k) (ex_ordered i)
  have h4 : maxdistIv (getAt eyList k.1) (getAt eyList (k.1 + 1)) (getAt exLoList i.1) (getAt exHiList (i.1 + 1)) =
      maxdistIv (getAt exLoList i.1) (getAt exHiList (i.1 + 1)) (getAt eyList k.1) (getAt eyList (k.1 + 1)) :=
    maxdistIv_comm _ _ _ _
  rw [h1, h2, h3, h4]
  set dxMin := distIv (getAt exLoList i.1) (getAt exHiList (i.1 + 1)) (getAt eyList k.1) (getAt eyList (k.1 + 1))
  set dxMax := maxdistIv (getAt exLoList i.1) (getAt exHiList (i.1 + 1)) (getAt eyList k.1) (getAt eyList (k.1 + 1))
  set dyMin := distIv (getAt eyList j.1) (getAt eyList (j.1 + 1)) (getAt exLoList l.1) (getAt exHiList (l.1 + 1))
  set dyMax := maxdistIv (getAt eyList j.1) (getAt eyList (j.1 + 1)) (getAt exLoList l.1) (getAt exHiList (l.1 + 1))
  have hdx_ord : dxMin ≤ dxMax := distIv_le_maxdistIv (ex_ordered i) (eyList_mono k)
  have hdy_ord : dyMin ≤ dyMax := distIv_le_maxdistIv (eyList_mono j) (ex_ordered l)
  by_cases hc : dxMax ≥ dyMin ∧ dyMax ≥ dxMin
  · have hc' : dyMax ≥ dxMin ∧ dxMax ≥ dyMin := ⟨hc.2, hc.1⟩
    rw [if_pos hc', if_pos hc]
  · have hc' : ¬(dyMax ≥ dxMin ∧ dxMax ≥ dyMin) := fun h => hc ⟨h.2, h.1⟩
    rw [if_neg hc', if_neg hc]
    by_cases hlt : dxMax < dyMin
    · have hnot : ¬(dyMax < dxMin) := by omega
      simp only [hlt, hnot, ↓reduceIte]
      congr 1
      ring
    · have hlt' : dyMax < dxMin := by omega
      simp only [hlt, hlt', ↓reduceIte]
      congr 1
      ring

private lemma M_int_gSwap (a b : Idx) : M_int (gSwap a) (gSwap b) = M_int a b := by
  rcases a with ⟨p, i, j⟩; rcases b with ⟨q, l, k⟩
  cases p <;> cases q
  · rfl
  · exact M12Int_swap i j l k
  · exact M12Int_swap l k i j
  · rfl

private lemma M_int_gFlipX (a b : Idx) : M_int (gFlipX a) (gFlipX b) = M_int a b := by
  have hexlo : ∀ m : Fin 14, getAt exLoList (rev14 m).1 = 10000 - getAt exHiList (m.1 + 1) := fun m => by
    have := exLoList_rev ⟨m.1 + 1, by omega⟩
    simpa [rev14, show 14 - (m.1 + 1) = 13 - m.1 by omega] using this
  have hexhi : ∀ m : Fin 14, getAt exHiList ((rev14 m).1 + 1) = 10000 - getAt exLoList m.1 := fun m => by
    have := exHiList_rev ⟨m.1, by omega⟩
    simpa [rev14, show (13 - m.1) + 1 = 14 - m.1 by omega] using this
  have heylo : ∀ m : Fin 14, getAt eyList (rev14 m).1 = 10000 - getAt eyList (m.1 + 1) := fun m => by
    have := eyList_rev ⟨m.1 + 1, by omega⟩
    simpa [rev14, show 14 - (m.1 + 1) = 13 - m.1 by omega] using this
  have heyhi : ∀ m : Fin 14, getAt eyList ((rev14 m).1 + 1) = 10000 - getAt eyList m.1 := fun m => by
    have := eyList_rev ⟨m.1, by omega⟩
    simpa [rev14, show (13 - m.1) + 1 = 14 - m.1 by omega] using this
  have hwx : ∀ m : Fin 14, getAt wxList (rev14 m).1 = getAt wxList m.1 := fun m => by
    simpa [rev14] using wxList_rev m
  rcases a with ⟨p, i, j⟩; rcases b with ⟨q, l, k⟩
  cases p <;> cases q
  · simp only [gFlipX, M_int, M1Int, hexlo, hexhi, hwx, maxdistIv_reflect]
  · simp only [gFlipX, M_int, M12Int, hexlo, hexhi, heylo, heyhi, hwx,
      maxdistIv_reflect]
    rw [distIv_reflect 10000 (ex_ordered i) (eyList_mono k)]
  · simp only [gFlipX, M_int, M12Int, hexlo, hexhi, heylo, heyhi, hwx,
      maxdistIv_reflect]
    rw [distIv_reflect 10000 (ex_ordered l) (eyList_mono j)]
  · simp only [gFlipX, M_int, M1Int, heylo, heyhi]
    rw [distIv_reflect 10000 (eyList_mono j) (eyList_mono k)]

private lemma M_int_gFlipY (a b : Idx) : M_int (gFlipY a) (gFlipY b) = M_int a b := by
  rw [gFlipY_eq a, gFlipY_eq b, M_int_gSwap, M_int_gFlipX, M_int_gSwap]

private lemma S_int_formula_base (i j : Fin 14) (hi : i.1 < 7) (hj : j.1 < 7) (q : Bool) (ci cj : Fin 14) :
    let r : ℕ := i.1 * 7 + j.1
    let c : ℕ := idx49 ci cj
    let aR : RowData := { idx := r, r0 := rowAt V0 r, r1 := rowAt V1 r, r2 := rowAt V2 r,
                          r3 := rowAt V3 r, r4t := rowAt V4top r, r4b := rowAt V4bot r }
    let bR : RowData := { idx := c, r0 := rowAt V0 c, r1 := rowAt V1 c, r2 := rowAt V2 c,
                          r3 := rowAt V3 c, r4t := rowAt V4top c, r4b := rowAt V4bot c }
    let g0 := dotL aR.r0 bR.r0
    let g1 := dotL aR.r1 bR.r1
    let g2 := dotL aR.r2 bR.r2
    let g3 := dotL aR.r3 bR.r3
    let g400 := dotL aR.r4t bR.r4t
    let g401 := dotL aR.r4t bR.r4b
    let g410 := dotL aR.r4b bR.r4t
    let g411 := dotL aR.r4b bR.r4b
    let fi := sgn7 ci
    let fj := sgn7 cj
    S_int (false, i, j) (q, ci, cj) =
      if q = false then (g0 + g1) + fi * fj * (g2 + g3) + fj * g400 + fi * g411
      else (g0 - g1) + fi * fj * (g2 - g3) + fi * g401 + fj * g410 := by
  intro r c aR bR g0 g1 g2 g3 g400 g401 g410 g411 fi fj
  have hr_lt : r < 49 := by dsimp [r]; omega
  have hc_lt : c < 49 := idx49_lt ci cj
  have hr_eq : idx49 i j = r := by simp [idx49, idx7, hi, hj, r]
  have hsi : sgn7 i = 1 := by simp [sgn7, hi]
  have hsj : sgn7 j = 1 := by simp [sgn7, hj]
  have hsp : sgnP false = 1 := rfl
  have hg0 : g0 = ∑ k : Fin 17, matAt V0 r k.1 * matAt V0 c k.1 :=
    dotL_eq_sum (rowAt_length V0_cols (V0_len ▸ hr_lt)) (rowAt_length V0_cols (V0_len ▸ hc_lt))
  have hg1 : g1 = ∑ k : Fin 18, matAt V1 r k.1 * matAt V1 c k.1 :=
    dotL_eq_sum (rowAt_length V1_cols (V1_len ▸ hr_lt)) (rowAt_length V1_cols (V1_len ▸ hc_lt))
  have hg2 : g2 = ∑ k : Fin 16, matAt V2 r k.1 * matAt V2 c k.1 :=
    dotL_eq_sum (rowAt_length V2_cols (V2_len ▸ hr_lt)) (rowAt_length V2_cols (V2_len ▸ hc_lt))
  have hg3 : g3 = ∑ k : Fin 17, matAt V3 r k.1 * matAt V3 c k.1 :=
    dotL_eq_sum (rowAt_length V3_cols (V3_len ▸ hr_lt)) (rowAt_length V3_cols (V3_len ▸ hc_lt))
  have hg400 : g400 = ∑ k : Fin 34, matAt V4top r k.1 * matAt V4top c k.1 :=
    dotL_eq_sum (rowAt_length V4top_cols (V4top_len ▸ hr_lt)) (rowAt_length V4top_cols (V4top_len ▸ hc_lt))
  have hg401 : g401 = ∑ k : Fin 34, matAt V4top r k.1 * matAt V4bot c k.1 :=
    dotL_eq_sum (rowAt_length V4top_cols (V4top_len ▸ hr_lt)) (rowAt_length V4bot_cols (V4bot_len ▸ hc_lt))
  have hg410 : g410 = ∑ k : Fin 34, matAt V4bot r k.1 * matAt V4top c k.1 :=
    dotL_eq_sum (rowAt_length V4bot_cols (V4bot_len ▸ hr_lt)) (rowAt_length V4top_cols (V4top_len ▸ hc_lt))
  have hg411 : g411 = ∑ k : Fin 34, matAt V4bot r k.1 * matAt V4bot c k.1 :=
    dotL_eq_sum (rowAt_length V4bot_cols (V4bot_len ▸ hr_lt)) (rowAt_length V4bot_cols (V4bot_len ▸ hc_lt))
  dsimp only [S_int, vec0, vec1, vec2, vec3, vec4a, vec4b]
  rw [hr_eq, hsi, hsj, hsp]
  cases q
  · simp only [sgnP, ↓reduceIte]
    rw [← hg0, show (∑ k : Fin 18, (1 * matAt V1 r k.1) * (1 * matAt V1 c k.1)) = g1 by
      rw [hg1]; refine Finset.sum_congr rfl fun _ _ => by ring]
    rw [show (∑ k : Fin 16, (1 * 1 * matAt V2 r k.1) * (fi * fj * matAt V2 c k.1)) = fi * fj * g2 by
      rw [hg2, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring]
    rw [show (∑ k : Fin 17, (1 * 1 * 1 * matAt V3 r k.1) * (1 * fi * fj * matAt V3 c k.1)) = fi * fj * g3 by
      rw [hg3, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring]
    rw [show (∑ k : Fin 34, (1 * matAt V4top r k.1) * (fj * matAt V4top c k.1)) = fj * g400 by
      rw [hg400, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring]
    rw [show (∑ k : Fin 34, (1 * matAt V4bot r k.1) * (fi * matAt V4bot c k.1)) = fi * g411 by
      rw [hg411, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring]
    ring
  · simp only [sgnP, Bool.true_eq_false, ↓reduceIte]
    rw [← hg0, show (∑ k : Fin 18, (1 * matAt V1 r k.1) * (-1 * matAt V1 c k.1)) = -g1 by
      rw [hg1, ← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun _ _ => by ring]
    rw [show (∑ k : Fin 16, (1 * 1 * matAt V2 r k.1) * (fi * fj * matAt V2 c k.1)) = fi * fj * g2 by
      rw [hg2, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring]
    rw [show (∑ k : Fin 17, (1 * 1 * 1 * matAt V3 r k.1) * (-1 * fi * fj * matAt V3 c k.1)) = -(fi * fj * g3) by
      rw [hg3, Finset.mul_sum, ← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun _ _ => by ring]
    rw [show (∑ k : Fin 34, (1 * matAt V4top r k.1) * (fi * matAt V4bot c k.1)) = fi * g401 by
      rw [hg401, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring]
    rw [show (∑ k : Fin 34, (1 * matAt V4bot r k.1) * (fj * matAt V4top c k.1)) = fj * g410 by
      rw [hg410, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring]
    ring

private lemma M_int_sub_S_int_ge_lam_base (i j : Fin 14) (hi : i.1 < 7) (hj : j.1 < 7)
    (b : Idx) :
    lamAt28 false i b.1 b.2.1 ≤ M_int (false, i, j) b - S_int (false, i, j) b := by
  rcases b with ⟨q, ci, cj⟩
  let r : ℕ := i.1 * 7 + j.1
  let c : ℕ := idx49 ci cj
  have hr_lt : r < 49 := by dsimp [r]; omega
  have hc_lt : c < 49 := idx49_lt ci cj
  have hchk := checkPair_all ⟨r, hr_lt⟩ ⟨c, hc_lt⟩
  dsimp only [checkPair] at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  have hri : r / 7 = i.1 := by dsimp [r]; omega
  have hrj : r % 7 = j.1 := by dsimp [r]; omega
  have hci : c / 7 = idx7 ci := by dsimp [c, idx49]; have := idx7_lt cj; omega
  have hcj : c % 7 = idx7 cj := by dsimp [c, idx49]; have := idx7_lt cj; omega
  rw [hri, hrj, hci, hcj] at hchk
  have hsf := S_int_formula_base i j hi hj q ci cj
  dsimp only [r, c] at hsf
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
  cases q
  · simp only [↓reduceIte] at hsf
    by_cases hci7 : ci.1 < 7 <;> by_cases hcj7 : cj.1 < 7
    · have hci_eq : idx7 ci = ci.1 := if_pos hci7
      have hcj_eq : idx7 cj = cj.1 := if_pos hcj7
      have hfi : sgn7 ci = 1 := if_pos hci7
      have hfj : sgn7 cj = 1 := if_pos hcj7
      simp only [hci_eq, hcj_eq] at h1
      rw [hfi, hfj] at hsf
      have heq : (dotL (rowAt V0 r) (rowAt V0 c) + dotL (rowAt V1 r) (rowAt V1 c) +
          (dotL (rowAt V2 r) (rowAt V2 c) + dotL (rowAt V3 r) (rowAt V3 c)) +
          dotL (rowAt V4top r) (rowAt V4top c) + dotL (rowAt V4bot r) (rowAt V4bot c)) =
          S_int (false, i, j) (false, ci, cj) := by rw [hsf]; ring
      rw [heq] at h1
      simpa [M_int, lamAt28, matAt, rowAt] using h1
    · have hci_eq : idx7 ci = ci.1 := if_pos hci7
      have hcj_eq : idx7 cj = 13 - cj.1 := if_neg hcj7
      have hcjn : 13 - (13 - cj.1) = cj.1 := by omega
      have hfi : sgn7 ci = 1 := if_pos hci7
      have hfj : sgn7 cj = -1 := if_neg hcj7
      simp only [hci_eq, hcj_eq, hcjn] at h2
      rw [hfi, hfj] at hsf
      have heq : (dotL (rowAt V0 r) (rowAt V0 c) + dotL (rowAt V1 r) (rowAt V1 c) -
          (dotL (rowAt V2 r) (rowAt V2 c) + dotL (rowAt V3 r) (rowAt V3 c)) -
          dotL (rowAt V4top r) (rowAt V4top c) + dotL (rowAt V4bot r) (rowAt V4bot c)) =
          S_int (false, i, j) (false, ci, cj) := by rw [hsf]; ring
      rw [heq] at h2
      simpa [M_int, lamAt28, matAt, rowAt] using h2
    · have hci_eq : idx7 ci = 13 - ci.1 := if_neg hci7
      have hcj_eq : idx7 cj = cj.1 := if_pos hcj7
      have hcin : 13 - (13 - ci.1) = ci.1 := by omega
      have hfi : sgn7 ci = -1 := if_neg hci7
      have hfj : sgn7 cj = 1 := if_pos hcj7
      simp only [hci_eq, hcj_eq, hcin] at h3
      rw [hfi, hfj] at hsf
      have heq : (dotL (rowAt V0 r) (rowAt V0 c) + dotL (rowAt V1 r) (rowAt V1 c) -
          (dotL (rowAt V2 r) (rowAt V2 c) + dotL (rowAt V3 r) (rowAt V3 c)) +
          dotL (rowAt V4top r) (rowAt V4top c) - dotL (rowAt V4bot r) (rowAt V4bot c)) =
          S_int (false, i, j) (false, ci, cj) := by rw [hsf]; ring
      rw [heq] at h3
      simpa [M_int, lamAt28, matAt, rowAt] using h3
    · have hci_eq : idx7 ci = 13 - ci.1 := if_neg hci7
      have hcj_eq : idx7 cj = 13 - cj.1 := if_neg hcj7
      have hcin : 13 - (13 - ci.1) = ci.1 := by omega
      have hcjn : 13 - (13 - cj.1) = cj.1 := by omega
      have hfi : sgn7 ci = -1 := if_neg hci7
      have hfj : sgn7 cj = -1 := if_neg hcj7
      simp only [hci_eq, hcj_eq, hcin, hcjn] at h4
      rw [hfi, hfj] at hsf
      have heq : (dotL (rowAt V0 r) (rowAt V0 c) + dotL (rowAt V1 r) (rowAt V1 c) +
          (dotL (rowAt V2 r) (rowAt V2 c) + dotL (rowAt V3 r) (rowAt V3 c)) -
          dotL (rowAt V4top r) (rowAt V4top c) - dotL (rowAt V4bot r) (rowAt V4bot c)) =
          S_int (false, i, j) (false, ci, cj) := by rw [hsf]; ring
      rw [heq] at h4
      simpa [M_int, lamAt28, matAt, rowAt] using h4
  · simp only [Bool.true_eq_false, ↓reduceIte] at hsf
    by_cases hci7 : ci.1 < 7 <;> by_cases hcj7 : cj.1 < 7
    · have hci_eq : idx7 ci = ci.1 := if_pos hci7
      have hcj_eq : idx7 cj = cj.1 := if_pos hcj7
      have hfi : sgn7 ci = 1 := if_pos hci7
      have hfj : sgn7 cj = 1 := if_pos hcj7
      simp only [hci_eq, hcj_eq] at h5
      rw [hfi, hfj] at hsf
      have heq : (dotL (rowAt V0 r) (rowAt V0 c) - dotL (rowAt V1 r) (rowAt V1 c) +
          (dotL (rowAt V2 r) (rowAt V2 c) - dotL (rowAt V3 r) (rowAt V3 c)) +
          dotL (rowAt V4top r) (rowAt V4bot c) + dotL (rowAt V4bot r) (rowAt V4top c)) =
          S_int (false, i, j) (true, ci, cj) := by rw [hsf]; ring
      rw [heq] at h5
      simpa [M_int, lamAt28, matAt, rowAt] using h5
    · have hci_eq : idx7 ci = ci.1 := if_pos hci7
      have hcj_eq : idx7 cj = 13 - cj.1 := if_neg hcj7
      have hcjn : 13 - (13 - cj.1) = cj.1 := by omega
      have hfi : sgn7 ci = 1 := if_pos hci7
      have hfj : sgn7 cj = -1 := if_neg hcj7
      simp only [hci_eq, hcj_eq, hcjn] at h6
      rw [hfi, hfj] at hsf
      have heq : (dotL (rowAt V0 r) (rowAt V0 c) - dotL (rowAt V1 r) (rowAt V1 c) -
          (dotL (rowAt V2 r) (rowAt V2 c) - dotL (rowAt V3 r) (rowAt V3 c)) +
          dotL (rowAt V4top r) (rowAt V4bot c) - dotL (rowAt V4bot r) (rowAt V4top c)) =
          S_int (false, i, j) (true, ci, cj) := by rw [hsf]; ring
      rw [heq] at h6
      simpa [M_int, lamAt28, matAt, rowAt] using h6
    · have hci_eq : idx7 ci = 13 - ci.1 := if_neg hci7
      have hcj_eq : idx7 cj = cj.1 := if_pos hcj7
      have hcin : 13 - (13 - ci.1) = ci.1 := by omega
      have hfi : sgn7 ci = -1 := if_neg hci7
      have hfj : sgn7 cj = 1 := if_pos hcj7
      simp only [hci_eq, hcj_eq, hcin] at h7
      rw [hfi, hfj] at hsf
      have heq : (dotL (rowAt V0 r) (rowAt V0 c) - dotL (rowAt V1 r) (rowAt V1 c) -
          (dotL (rowAt V2 r) (rowAt V2 c) - dotL (rowAt V3 r) (rowAt V3 c)) -
          dotL (rowAt V4top r) (rowAt V4bot c) + dotL (rowAt V4bot r) (rowAt V4top c)) =
          S_int (false, i, j) (true, ci, cj) := by rw [hsf]; ring
      rw [heq] at h7
      simpa [M_int, lamAt28, matAt, rowAt] using h7
    · have hci_eq : idx7 ci = 13 - ci.1 := if_neg hci7
      have hcj_eq : idx7 cj = 13 - cj.1 := if_neg hcj7
      have hcin : 13 - (13 - ci.1) = ci.1 := by omega
      have hcjn : 13 - (13 - cj.1) = cj.1 := by omega
      have hfi : sgn7 ci = -1 := if_neg hci7
      have hfj : sgn7 cj = -1 := if_neg hcj7
      simp only [hci_eq, hcj_eq, hcin, hcjn] at h8
      rw [hfi, hfj] at hsf
      have heq : (dotL (rowAt V0 r) (rowAt V0 c) - dotL (rowAt V1 r) (rowAt V1 c) +
          (dotL (rowAt V2 r) (rowAt V2 c) - dotL (rowAt V3 r) (rowAt V3 c)) -
          dotL (rowAt V4top r) (rowAt V4bot c) - dotL (rowAt V4bot r) (rowAt V4top c)) =
          S_int (false, i, j) (true, ci, cj) := by rw [hsf]; ring
      rw [heq] at h8
      simpa [M_int, lamAt28, matAt, rowAt] using h8

private lemma M_int_sub_S_int_ge_lam (a b : Idx) :
    lamAt28 a.1 a.2.1 b.1 b.2.1 ≤ M_int a b - S_int a b := by
  have hstep1 : ∀ a' b' : Idx, a'.1 = false →
      lamAt28 a'.1 a'.2.1 b'.1 b'.2.1 ≤ M_int a' b' - S_int a' b' := by
    rintro ⟨p', i', j'⟩ b' hp'
    subst hp'
    by_cases hi : i'.1 < 7 <;> by_cases hj : j'.1 < 7
    · exact M_int_sub_S_int_ge_lam_base i' j' hi hj b'
    · have hjrev : (rev14 j').1 < 7 := by dsimp [rev14]; omega
      have hbase := M_int_sub_S_int_ge_lam_base i' (rev14 j') hi hjrev (gFlipY b')
      have hlam : lamAt28 false i' (gFlipY b').1 (gFlipY b').2.1 = lamAt28 false i' b'.1 b'.2.1 := by
        rcases b' with ⟨q, ci, cj⟩
        cases q
        · rfl
        · simpa [gFlipY] using lamAt28_flipY false true i' ci
      have hms : M_int (false, i', rev14 j') (gFlipY b') - S_int (false, i', rev14 j') (gFlipY b') =
          M_int (false, i', j') b' - S_int (false, i', j') b' := by
        change M_int (gFlipY (false, i', j')) (gFlipY b') - S_int (gFlipY (false, i', j')) (gFlipY b') = _
        rw [M_int_gFlipY, S_int_gFlipY]
      linarith
    · have hirev : (rev14 i').1 < 7 := by dsimp [rev14]; omega
      have hbase := M_int_sub_S_int_ge_lam_base (rev14 i') j' hirev hj (gFlipX b')
      have hlam : lamAt28 false (rev14 i') (gFlipX b').1 (gFlipX b').2.1 = lamAt28 false i' b'.1 b'.2.1 := by
        rcases b' with ⟨q, ci, cj⟩
        cases q
        · simpa [gFlipX] using lamAt28_flipX false false i' ci
        · simpa [gFlipX] using lamAt28_flipX false true i' ci
      have hms : M_int (false, rev14 i', j') (gFlipX b') - S_int (false, rev14 i', j') (gFlipX b') =
          M_int (false, i', j') b' - S_int (false, i', j') b' := by
        change M_int (gFlipX (false, i', j')) (gFlipX b') - S_int (gFlipX (false, i', j')) (gFlipX b') = _
        rw [M_int_gFlipX, S_int_gFlipX]
      linarith
    · have hirev : (rev14 i').1 < 7 := by dsimp [rev14]; omega
      have hjrev : (rev14 j').1 < 7 := by dsimp [rev14]; omega
      have hbase := M_int_sub_S_int_ge_lam_base (rev14 i') (rev14 j') hirev hjrev (gFlipY (gFlipX b'))
      have hlam : lamAt28 false (rev14 i') (gFlipY (gFlipX b')).1 (gFlipY (gFlipX b')).2.1 =
          lamAt28 false i' b'.1 b'.2.1 := by
        rcases b' with ⟨q, ci, cj⟩
        cases q
        · simpa [gFlipX, gFlipY] using lamAt28_flipX false false i' ci
        · have hfx := lamAt28_flipX false true i' ci
          have hfy := lamAt28_flipY false true (rev14 i') ci
          simp only [Bool.true_eq_false, ↓reduceIte] at hfx
          simp only [↓reduceIte] at hfy
          simpa [gFlipX, gFlipY] using hfy.trans hfx
      have hms : M_int (false, rev14 i', rev14 j') (gFlipY (gFlipX b')) -
          S_int (false, rev14 i', rev14 j') (gFlipY (gFlipX b')) =
          M_int (false, i', j') b' - S_int (false, i', j') b' := by
        change M_int (gFlipY (gFlipX (false, i', j'))) (gFlipY (gFlipX b')) -
          S_int (gFlipY (gFlipX (false, i', j'))) (gFlipY (gFlipX b')) = _
        rw [M_int_gFlipY, M_int_gFlipX, S_int_gFlipY, S_int_gFlipX]
      linarith
  rcases a with ⟨p, i, j⟩
  cases p
  · exact hstep1 (false, i, j) b rfl
  · have hb := hstep1 (false, i, j) (gSwap b) rfl
    have hlam : lamAt28 false i (gSwap b).1 (gSwap b).2.1 = lamAt28 true i b.1 b.2.1 := by
      rcases b with ⟨q, ci, cj⟩
      have hsw := lamAt28_swap true q i ci
      simpa [gSwap] using hsw
    have hms : M_int (false, i, j) (gSwap b) - S_int (false, i, j) (gSwap b) =
        M_int (true, i, j) b - S_int (true, i, j) b := by
      change M_int (gSwap (true, i, j)) (gSwap b) - S_int (gSwap (true, i, j)) (gSwap b) = _
      rw [M_int_gSwap, S_int_gSwap]
    linarith

private lemma energyRat_lower_bound {z : Idx → ℝ} (hz0 : ∀ a, 0 ≤ z a)
    (hzsum : ∀ p : Bool, ∀ i : Fin 14, ∑ j : Fin 14, z (p, i, j) = 1) :
    8560536 ≤ ∑ a : Idx, ∑ b : Idx, z a * z b * (M_int a b : ℝ) := by
  have hge_pt : ∀ a b : Idx,
      z a * z b * ((S_int a b : ℝ) + (lamAt28 a.1 a.2.1 b.1 b.2.1 : ℝ)) ≤
      z a * z b * (M_int a b : ℝ) := fun a b => by
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hz0 a) (hz0 b))
    have h1 : (S_int a b + lamAt28 a.1 a.2.1 b.1 b.2.1 : ℝ) ≤ (M_int a b : ℝ) := by
      exact_mod_cast show S_int a b + lamAt28 a.1 a.2.1 b.1 b.2.1 ≤ M_int a b by
        linarith [M_int_sub_S_int_ge_lam a b]
    exact h1
  have hsplit : (∑ a : Idx, ∑ b : Idx, z a * z b * ((S_int a b : ℝ) + (lamAt28 a.1 a.2.1 b.1 b.2.1 : ℝ))) =
      (∑ a : Idx, ∑ b : Idx, z a * z b * (S_int a b : ℝ)) +
      (∑ a : Idx, ∑ b : Idx, z a * z b * (lamAt28 a.1 a.2.1 b.1 b.2.1 : ℝ)) := by
    simp only [mul_add, Finset.sum_add_distrib]
  have hsum_le := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => hge_pt a b
  have hlam_sum : (∑ a : Idx, ∑ b : Idx, z a * z b * (lamAt28 a.1 a.2.1 b.1 b.2.1 : ℝ)) = 8560536 := by
    have h1 : (∑ a : Idx, ∑ b : Idx, z a * z b * (lamAt28 a.1 a.2.1 b.1 b.2.1 : ℝ)) =
        ∑ p : Bool, ∑ i : Fin 14, ∑ q : Bool, ∑ l : Fin 14, (lamAt28 p i q l : ℝ) := by
      simp only [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => ?_
      have hinner : ∀ j : Fin 14,
          (∑ q : Bool, ∑ l : Fin 14, ∑ k : Fin 14,
            z (p, i, j) * z (q, l, k) * (lamAt28 p i q l : ℝ)) =
          z (p, i, j) * ∑ q : Bool, ∑ l : Fin 14, (lamAt28 p i q l : ℝ) := fun j => by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        calc (∑ k : Fin 14, z (p, i, j) * z (q, l, k) * (lamAt28 p i q l : ℝ))
            = ∑ k : Fin 14, (z (p, i, j) * (lamAt28 p i q l : ℝ)) * z (q, l, k) := by
              refine Finset.sum_congr rfl fun k _ => by ring
          _ = (z (p, i, j) * (lamAt28 p i q l : ℝ)) * ∑ k : Fin 14, z (q, l, k) := by
              rw [← Finset.mul_sum]
          _ = z (p, i, j) * (lamAt28 p i q l : ℝ) := by rw [hzsum q l, mul_one]
      simp_rw [hinner, ← Finset.sum_mul, hzsum p i, one_mul]
    rw [h1]
    exact_mod_cast sum_lamAt28
  linarith [hsum_le, hsplit, hlam_sum, S_int_psd z]

end Erdos1043WeakProof

theorem OMA.solution : type_of% @Erdos1043.erdos_1043.variants.weak := by
  intro f hf hd
  by_cases h1 : MeasureTheory.volume ((ℝ ∙ (1 : ℂ)).orthogonalProjectionOnto '' Erdos1043.levelSet f) ≤ 3.3
  · exact ⟨1, norm_one, h1⟩
  · by_cases hI : MeasureTheory.volume ((ℝ ∙ Complex.I).orthogonalProjectionOnto '' Erdos1043.levelSet f) ≤ 3.3
    · exact ⟨Complex.I, Complex.norm_I, hI⟩
    · exfalso
      push Not at h1 hI
      rw [volume_projection_one] at h1
      rw [volume_projection_I] at hI
      have hK := isCompact_levelSet hf hd
      have hReFin : MeasureTheory.volume (Complex.re '' Erdos1043.levelSet f) ≠ ⊤ :=
        (hK.image Complex.continuous_re).measure_lt_top.ne
      have hImFin : MeasureTheory.volume (Complex.im '' Erdos1043.levelSet f) ≠ ⊤ :=
        (hK.image Complex.continuous_im).measure_lt_top.ne
      have h33_nn : (3.3 : NNReal) = 33 / 10 := by norm_num
      have h33_eq : (3.3 : ENNReal) = ((33 / 10 : NNReal) : ENNReal) := by
        rw [← h33_nn]
        rfl
      have h33_fin : (3.3 : ENNReal) ≠ ⊤ := by
        rw [h33_eq]
        exact ENNReal.coe_ne_top
      have h33_real : (3.3 : ENNReal).toReal = (3.3 : ℝ) := by
        rw [h33_eq, ENNReal.coe_toReal]
        norm_num
      have hReGt : (3.3 : ℝ) < (MeasureTheory.volume (Complex.re '' Erdos1043.levelSet f)).toReal := by
        rw [← h33_real]
        exact ENNReal.toReal_lt_toReal h33_fin hReFin |>.mpr h1
      have hImGt : (3.3 : ℝ) < (MeasureTheory.volume (Complex.im '' Erdos1043.levelSet f)).toReal := by
        rw [← h33_real]
        exact ENNReal.toReal_lt_toReal h33_fin hImFin |>.mpr hI
      obtain ⟨z₀, -, hy_mem, hu_mem, hm_y, hm_u, hE_ub⟩ := energyRat_upper_bound hf hd hReGt hImGt
      have hge := energyRat_ge_M_int hm_y hm_u hy_mem hu_mem
      have hlb := energyRat_lower_bound
        (zVec_nonneg (yFn (Erdos1043.levelSet f) z₀) (uFn (Erdos1043.levelSet f) z₀))
        (zVec_row_sum hy_mem hu_mem hm_y hm_u)
      linarith
