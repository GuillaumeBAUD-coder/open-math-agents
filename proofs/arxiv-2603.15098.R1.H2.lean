import OMAReductions.R_arxiv_2603_15098_R1

/-!
# Proof of `arxiv-2603.15098.R1.H2`

Proves the Möbius normalization step for Koebe's circle-domain conjecture: every open connected
domain `U` in the Riemann sphere `OnePoint ℂ` can be mapped by a Möbius homeomorphism `g(p) = M • p`
to an open connected domain `g '' U` containing `∞`, such that conformal equivalences out of
`g '' U` pull back by precomposition with `g` to conformal equivalences out of `U`.
-/

open Set Filter Topology OMA.S_arxiv_2603_15098
open scoped OnePoint

namespace Arxiv260315098H2Proof

private lemma chart_self_infty : chart ∞ ∞ = 0 := by
  simp [chart, sphereInv, finiteCoord]

private lemma chart_self_coe (z : ℂ) : chart (z : Sphere) (z : Sphere) = z := by
  simp [chart, finiteCoord, OnePoint.coe_ne_infty]

private lemma chartSymm_self (p : Sphere) : chartSymm p (chart p p) = p := by
  induction p using OnePoint.rec with
  | infty => simp [chart, chartSymm, sphereInv, finiteCoord]
  | coe z => simp [chart, chartSymm, finiteCoord, OnePoint.coe_ne_infty]

private lemma chartSymm_chart_of_ne_zero {y : Sphere} (hy : y ≠ (0 : ℂ)) :
    chartSymm ∞ (chart ∞ y) = y := by
  induction y using OnePoint.rec with
  | infty => simp [chart, chartSymm, sphereInv, finiteCoord]
  | coe z =>
    have hz : z ≠ 0 := fun h => hy (by rw [h])
    simp [chart, chartSymm, sphereInv, finiteCoord, hz]

private lemma chartSymm_chart_of_ne_infty {w : ℂ} {y : Sphere} (hy : y ≠ ∞) :
    chartSymm (w : Sphere) (chart (w : Sphere) y) = y := by
  induction y using OnePoint.rec with
  | infty => exact (hy rfl).elim
  | coe z => simp [chart, chartSymm, finiteCoord, OnePoint.coe_ne_infty]

private lemma continuous_sphereInv_coe_at_zero :
    ContinuousAt (fun z : ℂ => sphereInv (z : Sphere)) 0 := by
  rw [ContinuousAt]
  have h0 : sphereInv ((0 : ℂ) : Sphere) = ∞ := by simp [sphereInv]
  rw [h0]
  rw [OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
  rintro K ⟨_, hKcomp⟩
  obtain ⟨R, hR⟩ := hKcomp.isBounded.subset_closedBall (0 : ℂ)
  have hRpos : 0 < max R 0 + 1 := by positivity
  refine Metric.eventually_nhds_iff.mpr ⟨(max R 0 + 1)⁻¹, by positivity, ?_⟩
  intro z hz
  rw [dist_zero_right] at hz
  by_cases hz0 : z = 0
  · simp [sphereInv, hz0]
  · have hsz : sphereInv (z : Sphere) = ((z⁻¹ : ℂ) : Sphere) := by simp [sphereInv, hz0]
    rw [hsz]
    left
    refine ⟨z⁻¹, ?_, rfl⟩
    intro hmem
    have hle : ‖z⁻¹‖ ≤ R := by
      have := hR hmem
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have hgt : max R 0 + 1 < ‖z⁻¹‖ := by
      rw [norm_inv, ← one_div, lt_div_iff₀ (norm_pos_iff.mpr hz0)]
      have hmul := mul_lt_mul_of_pos_left hz hRpos
      rwa [mul_inv_cancel₀ hRpos.ne'] at hmul
    linarith [le_max_left R 0]

private lemma continuousAt_chartSymm (p : Sphere) :
    ContinuousAt (chartSymm p) (chart p p) := by
  induction p using OnePoint.rec with
  | infty =>
    rw [chart_self_infty]
    have hfun : chartSymm ∞ = fun z : ℂ => sphereInv (z : Sphere) := by
      funext z; simp [chartSymm]
    rw [hfun]
    exact continuous_sphereInv_coe_at_zero
  | coe z =>
    rw [chart_self_coe]
    have hfun : chartSymm (z : Sphere) = OnePoint.some := by
      funext w; simp [chartSymm, OnePoint.coe_ne_infty]
    rw [hfun]
    exact OnePoint.continuous_coe.continuousAt

private lemma isConformalAt_comp {f g : Sphere → Sphere} {p : Sphere}
    (hf : IsConformalAt f (g p)) (hg : IsConformalAt g p) :
    IsConformalAt (f ∘ g) p := by
  refine ⟨hf.1.comp hg.1, ?_⟩
  rcases hf with ⟨_, df, hdf, hfd⟩
  rcases hg with ⟨hg_cont, dg, hdg, hgd⟩
  refine ⟨df * dg, mul_ne_zero hdf hdg, ?_⟩
  have hcomp : HasDerivAt
      (fun z => chart (f (g p)) (f (chartSymm (g p) (chart (g p) (g (chartSymm p z))))))
      (df * dg) (chart p p) := by
    have hval : chart (g p) (g (chartSymm p (chart p p))) = chart (g p) (g p) := by
      rw [chartSymm_self]
    have hfd' : HasDerivAt (fun w => chart (f (g p)) (f (chartSymm (g p) w))) df
        (chart (g p) (g (chartSymm p (chart p p)))) := hval.symm ▸ hfd
    exact hfd'.comp (chart p p) hgd
  refine hcomp.congr_of_eventuallyEq ?_
  have hcont : ContinuousAt (fun z => g (chartSymm p z)) (chart p p) := by
    have h1 := continuousAt_chartSymm p
    have h2 : ContinuousAt g (chartSymm p (chart p p)) := by
      rw [chartSymm_self]; exact hg_cont
    exact h2.comp h1
  have hmem : ∀ᶠ y in 𝓝 (g p), chartSymm (g p) (chart (g p) y) = y := by
    rcases eq_or_ne (g p) ∞ with hgp | hgp
    · rw [hgp]
      have hopen : IsOpen ({((0 : ℂ) : Sphere)}ᶜ : Set Sphere) := isClosed_singleton.isOpen_compl
      have hne : (∞ : Sphere) ∈ ({((0 : ℂ) : Sphere)}ᶜ : Set Sphere) := by
        simp [OnePoint.infty_ne_coe]
      filter_upwards [hopen.mem_nhds hne] with y hy
      exact chartSymm_chart_of_ne_zero hy
    · obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hgp
      rw [← hw]
      have hopen : IsOpen ({(∞ : Sphere)}ᶜ : Set Sphere) := OnePoint.isClosed_infty.isOpen_compl
      have hne : ((w : ℂ) : Sphere) ∈ ({(∞ : Sphere)}ᶜ : Set Sphere) := by
        simp [OnePoint.coe_ne_infty]
      filter_upwards [hopen.mem_nhds hne] with y hy
      exact chartSymm_chart_of_ne_infty hy
  have hpull : ∀ᶠ z in 𝓝 (chart p p),
      chartSymm (g p) (chart (g p) (g (chartSymm p z))) = g (chartSymm p z) := by
    have htend : Tendsto (fun z => g (chartSymm p z)) (𝓝 (chart p p)) (𝓝 (g p)) := by
      simpa [chartSymm_self] using hcont.tendsto
    exact htend.eventually hmem
  filter_upwards [hpull] with z hz
  simp only [Function.comp_apply, hz]

private lemma mobius_det_ne_zero (M : Mobius) : M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0 := by
  have h := M.det_ne_zero
  rwa [Matrix.det_fin_two] at h

private lemma continuous_mobius (M : Mobius) : Continuous (fun p : Sphere => M • p) := by
  set a := M 0 0
  set b := M 0 1
  set c := M 1 0
  set d := M 1 1
  have hdet : a * d - b * c ≠ 0 := mobius_det_ne_zero M
  have hsmul : ∀ z : ℂ, M • (z : Sphere) =
      if c * z + d = 0 then ∞ else (((a * z + b) / (c * z + d) : ℂ) : Sphere) :=
    fun _ => OnePoint.smul_some_eq_ite
  have hsmul_inf : M • (∞ : Sphere) = if c = 0 then ∞ else ((a / c : ℂ) : Sphere) :=
    OnePoint.smul_infty_eq_ite M
  rw [continuous_iff_continuousAt]
  intro p
  induction p using OnePoint.rec with
  | infty =>
    rw [OnePoint.continuousAt_infty']
    rw [hsmul_inf]
    by_cases hc : c = 0
    · simp only [hc, ↓reduceIte]
      have ha : a ≠ 0 := fun h => hdet (by simp [h, hc])
      have hd : d ≠ 0 := fun h => hdet (by simp [h, hc])
      have had : a / d ≠ 0 := div_ne_zero ha hd
      rw [OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
      rintro K ⟨_, hKcomp⟩
      obtain ⟨R, hR⟩ := hKcomp.isBounded.subset_closedBall (0 : ℂ)
      set R' := (max R 0 + ‖b / d‖ + 1) / ‖a / d‖
      have hmem : (Metric.closedBall (0 : ℂ) R')ᶜ ∈ Filter.coclosedCompact ℂ :=
        Filter.compl_mem_coclosedCompact.mpr
          (by rw [Metric.isClosed_closedBall.closure_eq]; exact isCompact_closedBall 0 R')
      filter_upwards [hmem] with z hz
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
      simp only [Function.comp_apply, hsmul, hc, zero_mul, zero_add, hd, ↓reduceIte]
      left
      refine ⟨(a * z + b) / d, ?_, rfl⟩
      intro hK
      have hle : ‖(a * z + b) / d‖ ≤ R := by
        have := hR hK
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      have heq : (a * z + b) / d = (a / d) * z + (b / d) := by ring
      rw [heq] at hle
      have htri : ‖(a / d) * z‖ - ‖b / d‖ ≤ ‖(a / d) * z + b / d‖ := by
        have h1 := norm_add_le ((a / d) * z + b / d) (-(b / d))
        simp only [add_neg_cancel_right, norm_neg] at h1
        linarith
      have hmul : max R 0 + ‖b / d‖ + 1 < ‖(a / d) * z‖ := by
        rw [norm_mul]
        have hpos : 0 < ‖a / d‖ := norm_pos_iff.mpr had
        have := (div_lt_iff₀ hpos).mp hz
        linarith
      linarith [le_max_left R 0]
    · simp only [hc, ↓reduceIte]
      rw [OnePoint.nhds_coe_eq]
      have htend : Tendsto (fun z : ℂ => (a * z + b) / (c * z + d))
          (Filter.coclosedCompact ℂ) (𝓝 (a / c)) := by
        rw [Metric.tendsto_nhds]
        intro ε hε
        have hnum_eq : ∀ z : ℂ, c * z + d ≠ 0 →
            (a * z + b) / (c * z + d) - a / c = (b * c - a * d) / (c * (c * z + d)) := by
          intro z hcz
          rw [div_sub_div _ _ hcz hc]
          congr 1
          · ring
          · ring
        set R := (‖b * c - a * d‖ / (ε * ‖c‖) + ‖d‖ + 1) / ‖c‖
        have hmem : (Metric.closedBall (0 : ℂ) R)ᶜ ∈ Filter.coclosedCompact ℂ :=
          Filter.compl_mem_coclosedCompact.mpr
            (by rw [Metric.isClosed_closedBall.closure_eq]; exact isCompact_closedBall 0 R)
        filter_upwards [hmem] with z hz
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
        have hcz_gt : ‖b * c - a * d‖ / (ε * ‖c‖) + 1 < ‖c * z + d‖ := by
          have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
          have h1 : ‖b * c - a * d‖ / (ε * ‖c‖) + ‖d‖ + 1 < ‖c * z‖ := by
            rw [norm_mul]
            have := (div_lt_iff₀ hcpos).mp hz
            linarith
          have htri : ‖c * z‖ - ‖d‖ ≤ ‖c * z + d‖ := by
            have h1 := norm_add_le (c * z + d) (-d)
            simp only [add_neg_cancel_right, norm_neg] at h1
            linarith
          linarith
        have hcz_pos : 0 < ‖c * z + d‖ := by
          have : 0 ≤ ‖b * c - a * d‖ / (ε * ‖c‖) := by positivity
          linarith
        have hcz_ne : c * z + d ≠ 0 := norm_pos_iff.mp hcz_pos
        rw [dist_eq_norm, hnum_eq z hcz_ne, norm_div, norm_mul]
        have hdenom_pos : 0 < ‖c‖ * ‖c * z + d‖ := mul_pos (norm_pos_iff.mpr hc) hcz_pos
        rw [div_lt_iff₀ hdenom_pos]
        have h1 : ‖b * c - a * d‖ / (ε * ‖c‖) < ‖c * z + d‖ := by linarith
        have h2 := (div_lt_iff₀ (mul_pos hε (norm_pos_iff.mpr hc))).mp h1
        linarith
      have hmap := OnePoint.continuous_coe.continuousAt.tendsto.comp htend
      rw [OnePoint.nhds_coe_eq] at hmap
      refine hmap.congr' ?_
      set R := (‖d‖ + 1) / ‖c‖
      have hmem : (Metric.closedBall (0 : ℂ) R)ᶜ ∈ Filter.coclosedCompact ℂ :=
        Filter.compl_mem_coclosedCompact.mpr
          (by rw [Metric.isClosed_closedBall.closure_eq]; exact isCompact_closedBall 0 R)
      filter_upwards [hmem] with z hz
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
      have hcz_ne : c * z + d ≠ 0 := by
        intro h
        have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
        have h1 : ‖d‖ + 1 < ‖c * z‖ := by
          rw [norm_mul]
          have := (div_lt_iff₀ hcpos).mp hz
          linarith
        have h2 : c * z = -d := eq_neg_of_add_eq_zero_left h
        rw [h2, norm_neg] at h1
        linarith
      simp [Function.comp_apply, hsmul, hcz_ne]
  | coe z₀ =>
    rw [OnePoint.continuousAt_coe]
    by_cases hden : c * z₀ + d = 0
    · have hc : c ≠ 0 := by
        intro hc0; rw [hc0, zero_mul, zero_add] at hden; exact hdet (by simp [hc0, hden])
      have hnum : a * z₀ + b ≠ 0 := by
        intro hnum0
        apply hdet
        have h1 : d = -(c * z₀) := eq_neg_of_add_eq_zero_right hden
        have h2 : b = -(a * z₀) := eq_neg_of_add_eq_zero_right hnum0
        rw [h1, h2]; ring
      rw [ContinuousAt]
      simp only [Function.comp_apply, hsmul, hden, ↓reduceIte]
      rw [OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
      rintro K ⟨_, hKcomp⟩
      obtain ⟨R, hR⟩ := hKcomp.isBounded.subset_closedBall (0 : ℂ)
      have hnum_pos : 0 < ‖a * z₀ + b‖ := norm_pos_iff.mpr hnum
      have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
      set δ1 := ‖a * z₀ + b‖ / (2 * (‖a‖ + 1))
      set δ2 := ‖a * z₀ + b‖ / (2 * ‖c‖ * (max R 0 + 1))
      refine Metric.eventually_nhds_iff.mpr ⟨min δ1 δ2, lt_min (by positivity) (by positivity), ?_⟩
      intro z hz
      have hz1 : ‖z - z₀‖ < δ1 := by rw [← dist_eq_norm]; exact lt_of_lt_of_le hz (min_le_left _ _)
      have hz2 : ‖z - z₀‖ < δ2 := by rw [← dist_eq_norm]; exact lt_of_lt_of_le hz (min_le_right _ _)
      by_cases hcz : c * z + d = 0
      · simp [Function.comp_apply, hsmul, hcz]
      · simp only [Function.comp_apply, hsmul, hcz, ↓reduceIte]
        left
        refine ⟨(a * z + b) / (c * z + d), ?_, rfl⟩
        intro hK
        have hle : ‖(a * z + b) / (c * z + d)‖ ≤ R := by
          have := hR hK
          rwa [Metric.mem_closedBall, dist_zero_right] at this
        have hcz_eq : c * z + d = c * (z - z₀) := by linear_combination hden
        have hnum_ge : ‖a * z₀ + b‖ / 2 ≤ ‖a * z + b‖ := by
          have htri : ‖a * z₀ + b‖ - ‖a * (z - z₀)‖ ≤ ‖a * z + b‖ := by
            have h1 := norm_add_le (a * z + b) (-(a * (z - z₀)))
            have heq2 : (a * z + b) + -(a * (z - z₀)) = a * z₀ + b := by ring
            rw [heq2, norm_neg] at h1
            linarith
          have ha_lt : ‖a * (z - z₀)‖ ≤ ‖a * z₀ + b‖ / 2 := by
            rw [norm_mul]
            have h1 : ‖z - z₀‖ * (2 * (‖a‖ + 1)) < ‖a * z₀ + b‖ :=
              (lt_div_iff₀ (by positivity)).mp hz1
            nlinarith [norm_nonneg (z - z₀), norm_nonneg a]
          linarith
        have hden_lt : ‖c * z + d‖ < ‖a * z₀ + b‖ / (2 * (max R 0 + 1)) := by
          rw [hcz_eq, norm_mul]
          have h1 : ‖z - z₀‖ * (2 * ‖c‖ * (max R 0 + 1)) < ‖a * z₀ + b‖ :=
            (lt_div_iff₀ (by positivity)).mp hz2
          rw [lt_div_iff₀ (by positivity)]
          linarith
        have hden_pos : 0 < ‖c * z + d‖ := norm_pos_iff.mpr hcz
        rw [norm_div, div_le_iff₀ hden_pos] at hle
        have hR0 : 0 ≤ max R 0 := le_max_right R 0
        have hle2 : R * ‖c * z + d‖ ≤ (max R 0 + 1) * ‖c * z + d‖ :=
          mul_le_mul_of_nonneg_right (by linarith [le_max_left R 0]) hden_pos.le
        have hlt3 : (max R 0 + 1) * ‖c * z + d‖ < ‖a * z₀ + b‖ / 2 := by
          have := mul_lt_mul_of_pos_left hden_lt (by positivity : (0 : ℝ) < max R 0 + 1)
          have heq3 : (max R 0 + 1) * (‖a * z₀ + b‖ / (2 * (max R 0 + 1))) =
              ‖a * z₀ + b‖ / 2 := by field_simp [show (max R 0 + 1 : ℝ) ≠ 0 by positivity]
          linarith
        linarith
    · have hcont : ContinuousAt (fun z : ℂ => (((a * z + b) / (c * z + d) : ℂ) : Sphere)) z₀ := by
        have h1 : ContinuousAt (fun z : ℂ => (a * z + b) / (c * z + d)) z₀ :=
          ((continuous_const.mul continuous_id).add continuous_const).continuousAt.div
            ((continuous_const.mul continuous_id).add continuous_const).continuousAt hden
        exact OnePoint.continuous_coe.continuousAt.comp h1
      refine hcont.congr ?_
      have hopen : IsOpen {z : ℂ | c * z + d ≠ 0} :=
        isOpen_ne.preimage ((continuous_const.mul continuous_id).add continuous_const)
      filter_upwards [hopen.mem_nhds hden] with z hz
      simp [Function.comp_apply, hsmul, hz]

private noncomputable def mobiusHomeo (M : Mobius) : Sphere ≃ₜ Sphere where
  toFun := fun p => M • p
  invFun := fun p => M⁻¹ • p
  left_inv := fun p => inv_smul_smul M p
  right_inv := fun p => smul_inv_smul M p
  continuous_toFun := continuous_mobius M
  continuous_invFun := continuous_mobius M⁻¹

private lemma isConformalOn_mobius (M : Mobius) :
    IsConformalOn (fun p : Sphere => M • p) Set.univ := by
  set a := M 0 0
  set b := M 0 1
  set c := M 1 0
  set d := M 1 1
  have hdet : a * d - b * c ≠ 0 := mobius_det_ne_zero M
  intro p _
  refine ⟨(continuous_mobius M).continuousAt, ?_⟩
  induction p using OnePoint.rec with
  | infty =>
    rw [chart_self_infty]
    by_cases hc : c = 0
    · have ha : a ≠ 0 := fun h => hdet (by simp [h, hc])
      have hd : d ≠ 0 := fun h => hdet (by simp [h, hc])
      refine ⟨d / a, div_ne_zero hd ha, ?_⟩
      have hderiv : HasDerivAt (fun w : ℂ => d * w / (a + b * w)) (d / a) 0 := by
        have hnum : HasDerivAt (fun w : ℂ => d * w) d 0 := by
          simpa using (hasDerivAt_id (0 : ℂ)).const_mul d
        have hden : HasDerivAt (fun w : ℂ => a + b * w) b 0 := by
          simpa using ((hasDerivAt_id (0 : ℂ)).const_mul b).const_add a
        have hq := hnum.div hden (by simpa using ha)
        refine hq.congr_deriv ?_
        field_simp [ha]
        ring
      refine hderiv.congr_of_eventuallyEq ?_
      have hopen : IsOpen {w : ℂ | a + b * w ≠ 0} :=
        isOpen_ne.preimage (continuous_const.add (continuous_const.mul continuous_id))
      have h0mem : (0 : ℂ) ∈ {w : ℂ | a + b * w ≠ 0} := by simpa using ha
      filter_upwards [hopen.mem_nhds h0mem] with w hw
      have hM_inf : M • (∞ : Sphere) = ∞ := by
        rw [OnePoint.smul_infty_eq_ite]
        simp [show M 1 0 = 0 from hc]
      rw [hM_inf]
      by_cases hw0 : w = 0
      · subst hw0
        simp [chart, chartSymm, sphereInv, finiteCoord, hM_inf]
      · have habw : (a * w⁻¹ + b) / d ≠ 0 := by
          intro h
          have h1 : a * w⁻¹ + b = 0 := (div_eq_zero_iff.mp h).resolve_right hd
          apply hw
          calc a + b * w = (a * w⁻¹ + b) * w := by field_simp [hw0]
            _ = 0 := by rw [h1, zero_mul]
        have hcs : chartSymm ∞ w = ((w⁻¹ : ℂ) : Sphere) := by simp [chartSymm, sphereInv, hw0]
        have hMw : M • ((w⁻¹ : ℂ) : Sphere) = (((a * w⁻¹ + b) / d : ℂ) : Sphere) := by
          rw [OnePoint.smul_some_eq_ite]
          change (if c * w⁻¹ + d = 0 then ∞ else (((a * w⁻¹ + b) / (c * w⁻¹ + d) : ℂ) : Sphere)) = _
          simp [hc, hd]
        rw [hcs, hMw]
        simp only [chart, sphereInv, finiteCoord, ↓reduceIte]
        have hinv_eq : sphereInv (((a * w⁻¹ + b) / d : ℂ) : Sphere) = ((((a * w⁻¹ + b) / d)⁻¹ : ℂ) : Sphere) := by
          simp [sphereInv, habw]
        change finiteCoord (sphereInv (((a * w⁻¹ + b) / d : ℂ) : Sphere)) = _
        rw [hinv_eq]
        change ((a * w⁻¹ + b) / d)⁻¹ = d * w / (a + b * w)
        field_simp [hw0, hd, hw]
    · refine ⟨(b * c - a * d) / c ^ 2, div_ne_zero (by intro h; apply hdet; linear_combination -h)
        (pow_ne_zero 2 hc), ?_⟩
      have hderiv : HasDerivAt (fun w : ℂ => (a + b * w) / (c + d * w))
          ((b * c - a * d) / c ^ 2) 0 := by
        have hnum : HasDerivAt (fun w : ℂ => a + b * w) b 0 := by
          simpa using ((hasDerivAt_id (0 : ℂ)).const_mul b).const_add a
        have hden : HasDerivAt (fun w : ℂ => c + d * w) d 0 := by
          simpa using ((hasDerivAt_id (0 : ℂ)).const_mul d).const_add c
        have hq := hnum.div hden (by simpa using hc)
        refine hq.congr_deriv ?_
        ring
      refine hderiv.congr_of_eventuallyEq ?_
      have hopen : IsOpen {w : ℂ | c + d * w ≠ 0} :=
        isOpen_ne.preimage (continuous_const.add (continuous_const.mul continuous_id))
      have h0mem : (0 : ℂ) ∈ {w : ℂ | c + d * w ≠ 0} := by simpa using hc
      filter_upwards [hopen.mem_nhds h0mem] with w hw
      have hM_inf : M • (∞ : Sphere) = ((a / c : ℂ) : Sphere) := by
        rw [OnePoint.smul_infty_eq_ite]
        change (if c = 0 then ∞ else ((a / c : ℂ) : Sphere)) = _
        simp [hc]
      rw [hM_inf]
      by_cases hw0 : w = 0
      · subst hw0
        simp [chart, chartSymm, sphereInv, finiteCoord, hM_inf, OnePoint.coe_ne_infty]
      · have hcw : c * w⁻¹ + d ≠ 0 := by
          intro h
          apply hw
          calc c + d * w = (c * w⁻¹ + d) * w := by field_simp [hw0]
            _ = 0 := by rw [h, zero_mul]
        have hcs : chartSymm ∞ w = ((w⁻¹ : ℂ) : Sphere) := by simp [chartSymm, sphereInv, hw0]
        have hMw : M • ((w⁻¹ : ℂ) : Sphere) = (((a * w⁻¹ + b) / (c * w⁻¹ + d) : ℂ) : Sphere) := by
          rw [OnePoint.smul_some_eq_ite]
          change (if c * w⁻¹ + d = 0 then ∞ else (((a * w⁻¹ + b) / (c * w⁻¹ + d) : ℂ) : Sphere)) = _
          simp [hcw]
        rw [hcs, hMw]
        have hch : chart ((a / c : ℂ) : Sphere) (((a * w⁻¹ + b) / (c * w⁻¹ + d) : ℂ) : Sphere) =
            (a * w⁻¹ + b) / (c * w⁻¹ + d) := by
          simp [chart, finiteCoord, OnePoint.coe_ne_infty]
        rw [hch]
        field_simp [hw0, hw]
  | coe z₀ =>
    rw [chart_self_coe]
    by_cases hden : c * z₀ + d = 0
    · have hc : c ≠ 0 := by
        intro hc0; rw [hc0, zero_mul, zero_add] at hden; exact hdet (by simp [hc0, hden])
      have hnum : a * z₀ + b ≠ 0 := by
        intro hnum0
        apply hdet
        have h1 : d = -(c * z₀) := eq_neg_of_add_eq_zero_right hden
        have h2 : b = -(a * z₀) := eq_neg_of_add_eq_zero_right hnum0
        rw [h1, h2]; ring
      refine ⟨c / (a * z₀ + b), div_ne_zero hc hnum, ?_⟩
      have hderiv : HasDerivAt (fun z : ℂ => (c * z + d) / (a * z + b))
          (c / (a * z₀ + b)) z₀ := by
        have hn : HasDerivAt (fun z : ℂ => c * z + d) c z₀ := by
          simpa using ((hasDerivAt_id z₀).const_mul c).add_const d
        have hd' : HasDerivAt (fun z : ℂ => a * z + b) a z₀ := by
          simpa using ((hasDerivAt_id z₀).const_mul a).add_const b
        have hq := hn.div hd' hnum
        refine hq.congr_deriv ?_
        rw [hden, zero_mul, sub_zero, sq]
        field_simp [hnum]
      refine hderiv.congr_of_eventuallyEq ?_
      have hopen : IsOpen {z : ℂ | a * z + b ≠ 0} :=
        isOpen_ne.preimage ((continuous_const.mul continuous_id).add continuous_const)
      filter_upwards [hopen.mem_nhds hnum] with z hz
      have hMz0 : M • (z₀ : Sphere) = ∞ := by
        rw [OnePoint.smul_some_eq_ite]
        change (if c * z₀ + d = 0 then ∞ else (((a * z₀ + b) / (c * z₀ + d) : ℂ) : Sphere)) = _
        simp [hden]
      rw [hMz0]
      by_cases hcz : c * z + d = 0
      · have hMz : M • (z : Sphere) = ∞ := by
          rw [OnePoint.smul_some_eq_ite]
          change (if c * z + d = 0 then ∞ else (((a * z + b) / (c * z + d) : ℂ) : Sphere)) = _
          simp [hcz]
        have hcs : chartSymm (z₀ : Sphere) z = (z : Sphere) := by simp [chartSymm, OnePoint.coe_ne_infty]
        rw [hcs, hMz, hcz, zero_div]
        simp [chart, sphereInv, finiteCoord]
      · have hdiv_ne : (a * z + b) / (c * z + d) ≠ 0 := div_ne_zero hz hcz
        have hcs : chartSymm (z₀ : Sphere) z = (z : Sphere) := by simp [chartSymm, OnePoint.coe_ne_infty]
        have hMz : M • (z : Sphere) = (((a * z + b) / (c * z + d) : ℂ) : Sphere) := by
          rw [OnePoint.smul_some_eq_ite]
          change (if c * z + d = 0 then ∞ else (((a * z + b) / (c * z + d) : ℂ) : Sphere)) = _
          simp [hcz]
        rw [hcs, hMz]
        have hch : chart ∞ (((a * z + b) / (c * z + d) : ℂ) : Sphere) =
            ((a * z + b) / (c * z + d))⁻¹ := by
          simp [chart, sphereInv, finiteCoord, hdiv_ne]
        rw [hch, inv_div]
    · refine ⟨(a * d - b * c) / (c * z₀ + d) ^ 2,
        div_ne_zero hdet (pow_ne_zero 2 hden), ?_⟩
      have hderiv : HasDerivAt (fun z : ℂ => (a * z + b) / (c * z + d))
          ((a * d - b * c) / (c * z₀ + d) ^ 2) z₀ := by
        have hn : HasDerivAt (fun z : ℂ => a * z + b) a z₀ := by
          simpa using ((hasDerivAt_id z₀).const_mul a).add_const b
        have hd' : HasDerivAt (fun z : ℂ => c * z + d) c z₀ := by
          simpa using ((hasDerivAt_id z₀).const_mul c).add_const d
        have hq := hn.div hd' hden
        refine hq.congr_deriv ?_
        ring
      refine hderiv.congr_of_eventuallyEq ?_
      have hopen : IsOpen {z : ℂ | c * z + d ≠ 0} :=
        isOpen_ne.preimage ((continuous_const.mul continuous_id).add continuous_const)
      filter_upwards [hopen.mem_nhds hden] with z hz
      have hMz0 : M • (z₀ : Sphere) = (((a * z₀ + b) / (c * z₀ + d) : ℂ) : Sphere) := by
        rw [OnePoint.smul_some_eq_ite]
        change (if c * z₀ + d = 0 then ∞ else (((a * z₀ + b) / (c * z₀ + d) : ℂ) : Sphere)) = _
        simp [hden]
      have hcs : chartSymm (z₀ : Sphere) z = (z : Sphere) := by simp [chartSymm, OnePoint.coe_ne_infty]
      have hMz : M • (z : Sphere) = (((a * z + b) / (c * z + d) : ℂ) : Sphere) := by
        rw [OnePoint.smul_some_eq_ite]
        change (if c * z + d = 0 then ∞ else (((a * z + b) / (c * z + d) : ℂ) : Sphere)) = _
        simp [hz]
      rw [hMz0, hcs, hMz]
      simp [chart, finiteCoord, OnePoint.coe_ne_infty]

private noncomputable def mobSwap (a : ℂ) : Mobius where
  val := !![(0 : ℂ), 1; 1, -a]
  inv := !![a, 1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private lemma mobSwap_apply_self (a : ℂ) : mobSwap a • (a : Sphere) = ∞ := by
  simp [OnePoint.smul_some_eq_ite, mobSwap]

private lemma exists_mobius_to_infty (p : Sphere) : ∃ M : Mobius, M • p = ∞ := by
  induction p using OnePoint.rec with
  | infty => exact ⟨1, one_smul _ _⟩
  | coe a => exact ⟨mobSwap a, mobSwap_apply_self a⟩


end Arxiv260315098H2Proof

theorem OMA.solution : OMA.R_arxiv_2603_15098_R1.H2 := by
  intro U hU hconn
  obtain ⟨p₀, hp₀⟩ := hconn.nonempty
  obtain ⟨M, hMp₀⟩ := Arxiv260315098H2Proof.exists_mobius_to_infty p₀
  let e := Arxiv260315098H2Proof.mobiusHomeo M
  refine ⟨e, e.isOpenMap U hU, hconn.image e e.continuous.continuousOn, ⟨p₀, hp₀, hMp₀⟩, ?_⟩
  intro V f hf
  rcases hf with ⟨hf_conf, hf_maps, hinv, hinv_conf, hinv_maps, hfg, hgf⟩
  refine ⟨?_, ?_, e.symm ∘ hinv, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact Arxiv260315098H2Proof.isConformalAt_comp
      (hf_conf (e p) ⟨p, hp, rfl⟩)
      (Arxiv260315098H2Proof.isConformalOn_mobius M p (mem_univ p))
  · intro p hp
    exact hf_maps ⟨p, hp, rfl⟩
  · intro w hw
    exact Arxiv260315098H2Proof.isConformalAt_comp
      (Arxiv260315098H2Proof.isConformalOn_mobius M⁻¹ (hinv w) (mem_univ _))
      (hinv_conf w hw)
  · intro w hw
    obtain ⟨p, hpU, hpeq⟩ := hinv_maps hw
    change e.symm (hinv w) ∈ U
    rw [← hpeq, e.symm_apply_apply]
    exact hpU
  · intro p hp
    change e.symm (hinv (f (e p))) = p
    rw [hfg (e p) ⟨p, hp, rfl⟩, e.symm_apply_apply]
  · intro w hw
    change f (e (e.symm (hinv w))) = w
    rw [e.apply_symm_apply, hgf w hw]
