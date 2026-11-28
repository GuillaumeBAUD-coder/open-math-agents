import OMAReductions.R_arxiv_2409_19103_R1

/-!
# Proof of `arxiv-2409.19103.R1.H2`

Proves the Möbius normalization step for the He–Schramm rigidity conjecture: given circle domains
`U, V` in the Riemann sphere `OnePoint ℂ` with `frontier U` conformally removable and a conformal
equivalence `f : U → V`, there exist Möbius transformations `A, B ∈ GL(2, ℂ)` such that
`G = A • U` is a circle domain containing `∞` with conformally removable frontier,
`g(p) = B • f(A⁻¹ • p)` is a conformal equivalence onto the circle domain `g '' G` fixing `∞`,
and `finiteCoord (g z) - z = O(z⁻¹)` on `Bornology.cobounded ℂ`.

First we establish that every `M ∈ GL(2, ℂ)` acts as a conformal homeomorphism of `OnePoint ℂ`,
preserving circle domains, conformal removability, and conformal equivalences. Then we choose `A`
moving a point `p₀ ∈ U` to `∞`, `B₀` moving `f p₀` to `∞`, and use three applications of
`Complex.differentiableOn_dslope` at `0` on the chart `φ(w) = chart ∞ (h₀ (chartSymm ∞ w))` to
extract `φ(w) = w (d + c₂ w + w² g₃(w))` with `d ≠ 0` and apply an affine Möbius map `S` so that
`B = S * B₀` achieves `finiteCoord (g z) - z = O(z⁻¹)`.
-/

open Set Filter Topology Asymptotics OMA.S_arxiv_2409_19103
open scoped OnePoint

namespace Arxiv240919103H2Proof

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

private lemma homeomorph_connectedComponentIn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (F : Set X) (x : X) :
    connectedComponentIn (e '' F) (e x) = e '' connectedComponentIn F x := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    have hmem : e x ∈ e '' F := by
      by_contra hnot
      have hemp : connectedComponentIn (e '' F) (e x) = ∅ := by simp [connectedComponentIn, hnot]
      rw [hemp] at hy
      exact hy
    have hconn : IsConnected (e.symm '' connectedComponentIn (e '' F) (e x)) := by
      have hpre : IsPreconnected (connectedComponentIn (e '' F) (e x)) :=
        isPreconnected_connectedComponentIn
      exact ⟨⟨x, ⟨e x, mem_connectedComponentIn hmem, e.symm_apply_apply x⟩⟩,
        hpre.image e.symm e.symm.continuous.continuousOn⟩
    have hsub : e.symm '' connectedComponentIn (e '' F) (e x) ⊆ F := by
      rintro z ⟨w, hw, rfl⟩
      have hw' : w ∈ e '' F := connectedComponentIn_subset (e '' F) (e x) hw
      rcases hw' with ⟨u, hu, rfl⟩
      simpa using hu
    have hxmem : x ∈ e.symm '' connectedComponentIn (e '' F) (e x) :=
      ⟨e x, mem_connectedComponentIn hmem, e.symm_apply_apply x⟩
    exact hconn.isPreconnected.subset_connectedComponentIn hxmem hsub ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    have hmem : x ∈ F := by
      by_contra hnot
      have hemp : connectedComponentIn F x = ∅ := by simp [connectedComponentIn, hnot]
      rw [hemp] at hz
      exact hz
    have hpre : IsPreconnected (e '' connectedComponentIn F x) :=
      isPreconnected_connectedComponentIn.image e e.continuous.continuousOn
    have hxmem : e x ∈ e '' connectedComponentIn F x :=
      ⟨x, mem_connectedComponentIn hmem, rfl⟩
    have hsub : e '' connectedComponentIn F x ⊆ e '' F :=
      image_mono (connectedComponentIn_subset F x)
    exact hpre.subset_connectedComponentIn hxmem hsub ⟨z, hz, rfl⟩

private lemma isCircleDomain_smul (M : Mobius) {W : Set Sphere} (hW : IsCircleDomain W) :
    IsCircleDomain ((fun p : Sphere => M • p) '' W) := by
  let e := mobiusHomeo M
  have hopen : IsOpen (e '' W) := e.isOpenMap W hW.1
  have hconn : IsConnected (e '' W) := hW.2.1.image e e.continuous.continuousOn
  refine ⟨hopen, hconn, ?_⟩
  intro p hp
  have hcompl : (e '' W)ᶜ = e '' Wᶜ := by
    ext x
    constructor
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      intro hmem
      exact hx ⟨e.symm x, hmem, e.apply_symm_apply x⟩
    · rintro ⟨u, hu, rfl⟩ ⟨v, hv, heq⟩
      exact hu ((e.injective heq) ▸ hv)
  change p ∈ (e '' W)ᶜ at hp
  change (∃ q, connectedComponentIn (e '' W)ᶜ p = {q}) ∨
    IsRoundClosedDisk (connectedComponentIn (e '' W)ᶜ p)
  rw [hcompl] at hp ⊢
  rcases hp with ⟨q, hq, rfl⟩
  rw [homeomorph_connectedComponentIn e Wᶜ q]
  rcases hW.2.2 q hq with ⟨r, hr⟩ | ⟨N, hN⟩
  · left
    exact ⟨e r, by rw [hr, image_singleton]⟩
  · right
    refine ⟨M * N, ?_⟩
    rw [hN, ← image_comp]
    congr 1
    ext x
    simp [e, mobiusHomeo, mul_smul]

private lemma isConformallyRemovable_smul (M : Mobius) {E : Set Sphere}
    (hE : IsConformallyRemovable E) :
    IsConformallyRemovable ((fun p : Sphere => M • p) '' E) := by
  let e := mobiusHomeo M
  refine ⟨hE.1.image e.continuous, ?_⟩
  intro h hh
  let h' : Sphere ≃ₜ Sphere := e.trans h
  have hh' : IsConformalOn h' Eᶜ := by
    intro p hp
    have hep : e p ∈ ((fun q : Sphere => M • q) '' E)ᶜ := by
      rintro ⟨q, hq, heq⟩
      exact hp (e.injective heq ▸ hq)
    have hcomp := isConformalAt_comp (hh (e p) hep) (isConformalOn_mobius M p (mem_univ p))
    exact hcomp
  obtain ⟨N, hN⟩ := hE.2 h' hh'
  refine ⟨N * M⁻¹, fun p => ?_⟩
  have h1 : h (M • (M⁻¹ • p)) = N • (M⁻¹ • p) := hN (M⁻¹ • p)
  rw [smul_inv_smul] at h1
  rw [h1, mul_smul]

private lemma isConformalEquivalence_conj {U V : Set Sphere} {f : Sphere → Sphere}
    (hf : IsConformalEquivalence f U V) (A B : Mobius) :
    IsConformalEquivalence (fun p => B • f (A⁻¹ • p))
      ((fun p => A • p) '' U) ((fun p => B • p) '' V) := by
  rcases hf with ⟨hf_conf, hf_maps, g, hg_conf, hg_maps, hgf, hfg⟩
  refine ⟨?_, ?_, fun w => A • g (B⁻¹ • w), ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases hp with ⟨u, hu, rfl⟩
    have h1 : IsConformalAt (fun q => B • q) (f (A⁻¹ • (A • u))) :=
      isConformalOn_mobius B _ (mem_univ _)
    have h2 : IsConformalAt f (A⁻¹ • (A • u)) := by
      rw [inv_smul_smul]; exact hf_conf u hu
    have h3 : IsConformalAt (fun q => A⁻¹ • q) (A • u) :=
      isConformalOn_mobius A⁻¹ _ (mem_univ _)
    exact isConformalAt_comp h1 (isConformalAt_comp h2 h3)
  · rintro p ⟨u, hu, rfl⟩
    dsimp only
    rw [inv_smul_smul]
    exact ⟨f u, hf_maps hu, rfl⟩
  · intro w hw
    rcases hw with ⟨v, hv, rfl⟩
    have h1 : IsConformalAt (fun q => A • q) (g (B⁻¹ • (B • v))) :=
      isConformalOn_mobius A _ (mem_univ _)
    have h2 : IsConformalAt g (B⁻¹ • (B • v)) := by
      rw [inv_smul_smul]; exact hg_conf v hv
    have h3 : IsConformalAt (fun q => B⁻¹ • q) (B • v) :=
      isConformalOn_mobius B⁻¹ _ (mem_univ _)
    exact isConformalAt_comp h1 (isConformalAt_comp h2 h3)
  · rintro w ⟨v, hv, rfl⟩
    dsimp only
    rw [inv_smul_smul]
    exact ⟨g v, hg_maps hv, rfl⟩
  · rintro p ⟨u, hu, rfl⟩
    simp [inv_smul_smul, hgf u hu]
  · rintro w ⟨v, hv, rfl⟩
    simp [inv_smul_smul, hfg v hv]

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

private noncomputable def mobAffine (d c : ℂ) (hd : d ≠ 0) : Mobius where
  val := !![d, c; 0, 1]
  inv := !![d⁻¹, -(c / d); 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hd, mul_div_cancel₀ _ hd]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hd]
    field_simp [hd]
    ring

private lemma mobAffine_apply_infty (d c : ℂ) (hd : d ≠ 0) :
    mobAffine d c hd • (∞ : Sphere) = ∞ := by
  simp [OnePoint.smul_infty_eq_ite, mobAffine]

private lemma mobAffine_apply_coe (d c : ℂ) (hd : d ≠ 0) (z : ℂ) :
    mobAffine d c hd • (z : Sphere) = ((d * z + c : ℂ) : Sphere) := by
  simp [OnePoint.smul_some_eq_ite, mobAffine]

private lemma exists_mobius_to_infty (p : Sphere) : ∃ M : Mobius, M • p = ∞ := by
  induction p using OnePoint.rec with
  | infty => exact ⟨1, one_smul _ _⟩
  | coe a => exact ⟨mobSwap a, mobSwap_apply_self a⟩

private lemma exists_affine_normalization {G W : Set Sphere} {h : Sphere → Sphere}
    (hGopen : IsOpen G) (hinf : ∞ ∈ G) (hh : IsConformalEquivalence h G W) (hfix : h ∞ = ∞) :
    ∃ (d c : ℂ) (hd : d ≠ 0),
      (fun z : ℂ => finiteCoord (mobAffine d c hd • h (z : Sphere)) - z)
        =O[Bornology.cobounded ℂ] (fun z : ℂ => z⁻¹) := by
  rcases hh with ⟨hh_conf, _, hinv, _, _, hinv_h, _⟩
  let φ : ℂ → ℂ := fun w => chart ∞ (h (chartSymm ∞ w))
  have hφ0 : φ 0 = 0 := by
    simp [φ, chart, chartSymm, sphereInv, finiteCoord, hfix]
  obtain ⟨_, d, hd, hφ_deriv0⟩ := hh_conf ∞ hinf
  rw [chart_self_infty, hfix] at hφ_deriv0
  -- Find a ball around 0 where chartSymm ∞ w ∈ G and for w ≠ 0, h (chartSymm ∞ w) is finite nonzero
  have hG_nhds : G ∈ 𝓝 (∞ : Sphere) := hGopen.mem_nhds hinf
  have hpreG : ∀ᶠ w in 𝓝 (0 : ℂ), chartSymm ∞ w ∈ G := by
    have hcont := continuousAt_chartSymm ∞
    rw [chart_self_infty] at hcont
    have htend : Tendsto (chartSymm ∞) (𝓝 (0 : ℂ)) (𝓝 (∞ : Sphere)) := by
      simpa [chartSymm, sphereInv] using hcont.tendsto
    exact htend.eventually hG_nhds
  have hpre_ne0 : ∀ᶠ w in 𝓝 (0 : ℂ), h (chartSymm ∞ w) ≠ (0 : ℂ) := by
    have hcont : ContinuousAt (fun w => h (chartSymm ∞ w)) 0 := by
      have h1 := continuousAt_chartSymm ∞
      rw [chart_self_infty] at h1
      have h2 : ContinuousAt h (chartSymm ∞ 0) := by
        simpa [chartSymm, sphereInv] using (hh_conf ∞ hinf).1
      exact h2.comp h1
    have hopen : IsOpen ({((0 : ℂ) : Sphere)}ᶜ : Set Sphere) := isClosed_singleton.isOpen_compl
    have hmem : h (chartSymm ∞ 0) ∈ ({((0 : ℂ) : Sphere)}ᶜ : Set Sphere) := by
      simp [chartSymm, sphereInv, hfix, OnePoint.infty_ne_coe]
    exact hcont.tendsto.eventually (hopen.mem_nhds hmem)
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.eventually_nhds_iff.mp (hpreG.and hpre_ne0)
  -- Show φ is DifferentiableOn ℂ on Metric.ball 0 r
  have hφ_diff : DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) r) := by
    intro w hw
    by_cases hw0 : w = 0
    · subst hw0
      exact hφ_deriv0.differentiableAt.differentiableWithinAt
    · have hball_mem := hr_sub hw
      have hwinG : ((w⁻¹ : ℂ) : Sphere) ∈ G := by
        simpa [chartSymm, sphereInv, hw0] using hball_mem.1
      have hne_inf : h ((w⁻¹ : ℂ) : Sphere) ≠ ∞ := by
        intro heq
        have hinj : ((w⁻¹ : ℂ) : Sphere) = ∞ := by
          calc ((w⁻¹ : ℂ) : Sphere) = hinv (h ((w⁻¹ : ℂ) : Sphere)) := (hinv_h _ hwinG).symm
            _ = hinv (h ∞) := by rw [heq, hfix]
            _ = ∞ := hinv_h ∞ hinf
        exact OnePoint.coe_ne_infty _ hinj
      obtain ⟨ζ, hζ⟩ := OnePoint.ne_infty_iff_exists.mp hne_inf
      have hζ_ne0 : ζ ≠ 0 := by
        intro h0
        apply hball_mem.2
        simpa [chartSymm, sphereInv, hw0, h0] using hζ.symm
      obtain ⟨hcont_w, dw, _, hderiv_w⟩ := hh_conf ((w⁻¹ : ℂ) : Sphere) hwinG
      rw [chart_self_coe, ← hζ] at hderiv_w
      have hinv_d : HasDerivAt (fun u : ℂ => u⁻¹) (-(w ^ 2)⁻¹) w := hasDerivAt_inv hw0
      have hcomp_d : HasDerivAt
          (fun u : ℂ => chart (ζ : Sphere) (h (chartSymm ((w⁻¹ : ℂ) : Sphere) u⁻¹)))
          (dw * -(w ^ 2)⁻¹) w := hderiv_w.comp w hinv_d
      have hval_eq : chart (ζ : Sphere) (h (chartSymm ((w⁻¹ : ℂ) : Sphere) w⁻¹)) = ζ := by
        simp [chart, chartSymm, finiteCoord, OnePoint.coe_ne_infty, ← hζ]
      have hinv_comp : HasDerivAt
          (fun u : ℂ => (chart (ζ : Sphere) (h (chartSymm ((w⁻¹ : ℂ) : Sphere) u⁻¹)))⁻¹)
          (-(dw * -(w ^ 2)⁻¹) / ζ ^ 2) w := by
        have := hcomp_d.inv (by rwa [hval_eq])
        rwa [hval_eq] at this
      have hφ_at_w : HasDerivAt φ (-(dw * -(w ^ 2)⁻¹) / ζ ^ 2) w := by
        refine hinv_comp.congr_of_eventuallyEq ?_
        have hopen_ball : IsOpen (Metric.ball (0 : ℂ) r \ {0}) :=
          Metric.isOpen_ball.sdiff isClosed_singleton
        have hw_in : w ∈ Metric.ball (0 : ℂ) r \ {0} := ⟨hw, hw0⟩
        filter_upwards [hopen_ball.mem_nhds hw_in] with u ⟨hu_ball, hu0⟩
        have hu0' : u ≠ 0 := hu0
        have hu_mem := hr_sub hu_ball
        have hu_inG : ((u⁻¹ : ℂ) : Sphere) ∈ G := by simpa [chartSymm, sphereInv, hu0'] using hu_mem.1
        have hu_ne_inf : h ((u⁻¹ : ℂ) : Sphere) ≠ ∞ := by
          intro heq
          have hinj : ((u⁻¹ : ℂ) : Sphere) = ∞ := by
            calc ((u⁻¹ : ℂ) : Sphere) = hinv (h ((u⁻¹ : ℂ) : Sphere)) := (hinv_h _ hu_inG).symm
              _ = hinv (h ∞) := by rw [heq, hfix]
              _ = ∞ := hinv_h ∞ hinf
          exact OnePoint.coe_ne_infty _ hinj
        obtain ⟨η, hη⟩ := OnePoint.ne_infty_iff_exists.mp hu_ne_inf
        have hη_ne0 : η ≠ 0 := by
          intro h0
          apply hu_mem.2
          simpa [chartSymm, sphereInv, hu0', h0] using hη.symm
        simp [φ, chart, chartSymm, sphereInv, finiteCoord, hu0', ← hη, hη_ne0]
      exact hφ_at_w.differentiableAt.differentiableWithinAt
  -- Apply `Complex.differentiableOn_dslope` three times at 0!
  have hs_nhds : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 hr_pos
  let g₁ : ℂ → ℂ := dslope φ 0
  have hg₁_diff : DifferentiableOn ℂ g₁ (Metric.ball (0 : ℂ) r) :=
    (Complex.differentiableOn_dslope hs_nhds).mpr hφ_diff
  have hg₁_0 : g₁ 0 = d := by
    dsimp [g₁]
    rw [dslope_same, hφ_deriv0.deriv]
  let g₂ : ℂ → ℂ := dslope g₁ 0
  have hg₂_diff : DifferentiableOn ℂ g₂ (Metric.ball (0 : ℂ) r) :=
    (Complex.differentiableOn_dslope hs_nhds).mpr hg₁_diff
  set c₂ : ℂ := g₂ 0
  let g₃ : ℂ → ℂ := dslope g₂ 0
  have hg₃_diff : DifferentiableOn ℂ g₃ (Metric.ball (0 : ℂ) r) :=
    (Complex.differentiableOn_dslope hs_nhds).mpr hg₂_diff
  -- Choose affine parameters d and c := c₂ / d
  refine ⟨d, c₂ / d, hd, ?_⟩
  -- Continuity of g₁, g₂, g₃ at 0 gives a uniform bound near 0
  have hg₁_cont : ContinuousAt g₁ 0 := hg₁_diff.continuousOn.continuousAt hs_nhds
  have hg₂_cont : ContinuousAt g₂ 0 := hg₂_diff.continuousOn.continuousAt hs_nhds
  have hg₃_cont : ContinuousAt g₃ 0 := hg₃_diff.continuousOn.continuousAt hs_nhds
  have hg₁_lb : ∀ᶠ w in 𝓝 (0 : ℂ), ‖d‖ / 2 ≤ ‖g₁ w‖ := by
    have hpos : 0 < ‖d‖ / 2 := by positivity
    have hmem : ∀ᶠ w in 𝓝 (0 : ℂ), dist (g₁ w) (g₁ 0) < ‖d‖ / 2 :=
      Metric.tendsto_nhds.mp hg₁_cont.tendsto (‖d‖ / 2) hpos
    filter_upwards [hmem] with w hw
    rw [hg₁_0, dist_eq_norm] at hw
    have htri := norm_sub_norm_le d (g₁ w)
    rw [norm_sub_rev] at htri
    linarith
  have hg₂_ub : ∀ᶠ w in 𝓝 (0 : ℂ), ‖g₂ w‖ ≤ ‖c₂‖ + 1 := by
    have hmem : ∀ᶠ w in 𝓝 (0 : ℂ), dist (g₂ w) (g₂ 0) < 1 :=
      Metric.tendsto_nhds.mp hg₂_cont.tendsto 1 zero_lt_one
    filter_upwards [hmem] with w hw
    rw [dist_eq_norm] at hw
    have htri := norm_sub_norm_le (g₂ w) c₂
    linarith
  have hg₃_ub : ∀ᶠ w in 𝓝 (0 : ℂ), ‖g₃ w‖ ≤ ‖g₃ 0‖ + 1 := by
    have hmem : ∀ᶠ w in 𝓝 (0 : ℂ), dist (g₃ w) (g₃ 0) < 1 :=
      Metric.tendsto_nhds.mp hg₃_cont.tendsto 1 zero_lt_one
    filter_upwards [hmem] with w hw
    rw [dist_eq_norm] at hw
    have htri := norm_sub_norm_le (g₃ w) (g₃ 0)
    linarith
  have hs_ev : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ Metric.ball (0 : ℂ) r := hs_nhds
  obtain ⟨δ, hδ_pos, hδ_prop⟩ := Metric.eventually_nhds_iff.mp
    (hs_ev.and (hg₁_lb.and (hg₂_ub.and hg₃_ub)))
  -- Bound on cobounded ℂ: for ‖z‖ > δ⁻¹, w = z⁻¹ ∈ ball 0 δ \ {0}
  set C : ℝ := (‖c₂‖ * (‖c₂‖ + 1) + ‖d‖ * (‖g₃ 0‖ + 1)) / (‖d‖ * (‖d‖ / 2))
  refine Asymptotics.isBigO_iff.mpr ⟨C, ?_⟩
  have hcb : (Metric.closedBall (0 : ℂ) δ⁻¹)ᶜ ∈ Bornology.cobounded ℂ :=
    Bornology.isBounded_def.mp Metric.isBounded_closedBall
  refine Filter.mem_of_superset hcb fun z hz => ?_
  change ‖finiteCoord (mobAffine d (c₂ / d) hd • h (z : Sphere)) - z‖ ≤ C * ‖z⁻¹‖
  have hz : δ⁻¹ < ‖z‖ := by
    simpa [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hz
  have hz_pos : 0 < ‖z‖ := lt_trans (inv_pos.mpr hδ_pos) hz
  have hz_ne0 : z ≠ 0 := norm_pos_iff.mp hz_pos
  set w : ℂ := z⁻¹
  have hw_ne0 : w ≠ 0 := inv_ne_zero hz_ne0
  have hw_lt : dist w 0 < δ := by
    rw [dist_zero_right, norm_inv]
    exact (inv_lt_iff_one_lt_mul₀ hz_pos).mpr <| by
      have := (inv_lt_iff_one_lt_mul₀ hδ_pos).mp hz
      linarith
  obtain ⟨hw_ball, hw_g1, hw_g2, hw_g3⟩ := hδ_prop hw_lt
  have hball_mem := hr_sub hw_ball
  have hz_inG : (z : Sphere) ∈ G := by
    have h1 : chartSymm ∞ w = (z : Sphere) := by simp [chartSymm, sphereInv, w, hw_ne0]
    exact h1 ▸ hball_mem.1
  have hz_ne_inf : h (z : Sphere) ≠ ∞ := by
    intro heq
    have hinj : (z : Sphere) = ∞ := by
      calc (z : Sphere) = hinv (h (z : Sphere)) := (hinv_h _ hz_inG).symm
        _ = hinv (h ∞) := by rw [heq, hfix]
        _ = ∞ := hinv_h ∞ hinf
    exact OnePoint.coe_ne_infty z hinj
  obtain ⟨ζ, hζ⟩ := OnePoint.ne_infty_iff_exists.mp hz_ne_inf
  have hζ_ne0 : ζ ≠ 0 := by
    intro h0
    apply hball_mem.2
    have h1 : chartSymm ∞ w = (z : Sphere) := by simp [chartSymm, sphereInv, w, hw_ne0]
    rw [h1, ← hζ, h0]
  have hφw : φ w = ζ⁻¹ := by
    have h1 : chartSymm ∞ w = (z : Sphere) := by simp [chartSymm, sphereInv, w, hw_ne0]
    simp [φ, h1, ← hζ, chart, sphereInv, finiteCoord, hζ_ne0]
  have hφ_eq : φ w = w * g₁ w := by
    have := sub_smul_dslope φ 0 w
    simpa [g₁, hφ0] using this.symm
  have hg1_eq : g₁ w = d + w * g₂ w := by
    have := sub_smul_dslope g₁ 0 w
    have hsub : w * g₂ w = g₁ w - d := by simpa [g₂, hg₁_0] using this
    linear_combination -hsub
  have hg2_eq : g₂ w = c₂ + w * g₃ w := by
    have := sub_smul_dslope g₂ 0 w
    have hsub : w * g₃ w = g₂ w - c₂ := by simpa [g₃, c₂] using this
    linear_combination -hsub
  have hg1_ne0 : g₁ w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw_g1
    have : 0 < ‖d‖ / 2 := by positivity
    linarith
  have hζ_eq : ζ = (w * g₁ w)⁻¹ := by
    have h1 : ζ⁻¹ = w * g₁ w := hφw.symm.trans hφ_eq
    rw [← h1, inv_inv]
  have hval : finiteCoord (mobAffine d (c₂ / d) hd • h (z : Sphere)) - z =
      w * ((c₂ * g₂ w - d * g₃ w) / (d * g₁ w)) := by
    rw [← hζ, mobAffine_apply_coe]
    have hfc : finiteCoord (((d * ζ + c₂ / d : ℂ) : Sphere)) = d * ζ + c₂ / d := rfl
    rw [hfc, hζ_eq]
    have hz_w : z = w⁻¹ := (inv_inv z).symm
    rw [hz_w]
    have hdenom : d * g₁ w ≠ 0 := mul_ne_zero hd hg1_ne0
    have hcalc : d * (w * g₁ w)⁻¹ + c₂ / d - w⁻¹ =
        (d ^ 2 + c₂ * w * g₁ w - d * g₁ w) / (d * w * g₁ w) := by
      field_simp [hd, hw_ne0, hg1_ne0]
    rw [hcalc]
    have hnum : d ^ 2 + c₂ * w * g₁ w - d * g₁ w = w ^ 2 * (c₂ * g₂ w - d * g₃ w) := by
      rw [hg1_eq]
      have h1 : d ^ 2 + c₂ * w * (d + w * g₂ w) - d * (d + w * g₂ w) =
          w ^ 2 * c₂ * g₂ w - d * w * (g₂ w - c₂) := by ring
      rw [h1, hg2_eq]
      ring
    rw [hnum]
    field_simp [hd, hw_ne0, hg1_ne0]
  rw [hval, norm_mul, norm_div, norm_mul]
  have hnum_le : ‖c₂ * g₂ w - d * g₃ w‖ ≤ ‖c₂‖ * (‖c₂‖ + 1) + ‖d‖ * (‖g₃ 0‖ + 1) := by
    calc ‖c₂ * g₂ w - d * g₃ w‖
        ≤ ‖c₂ * g₂ w‖ + ‖d * g₃ w‖ := norm_sub_le _ _
      _ = ‖c₂‖ * ‖g₂ w‖ + ‖d‖ * ‖g₃ w‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖c₂‖ * (‖c₂‖ + 1) + ‖d‖ * (‖g₃ 0‖ + 1) := by
          gcongr
  have hden_ge : ‖d‖ * (‖d‖ / 2) ≤ ‖d‖ * ‖g₁ w‖ := by gcongr
  have hden_pos : 0 < ‖d‖ * (‖d‖ / 2) := by positivity
  have hfrac : ‖c₂ * g₂ w - d * g₃ w‖ / (‖d‖ * ‖g₁ w‖) ≤ C := by
    dsimp [C]
    exact div_le_div₀ (by positivity) hnum_le hden_pos hden_ge
  calc ‖w‖ * (‖c₂ * g₂ w - d * g₃ w‖ / (‖d‖ * ‖g₁ w‖))
      ≤ ‖w‖ * C := mul_le_mul_of_nonneg_left hfrac (norm_nonneg w)
    _ = C * ‖z⁻¹‖ := by ring

end Arxiv240919103H2Proof

theorem OMA.solution : OMA.R_arxiv_2409_19103_R1.H2 := by
  intro U V f hU hV hrem hf
  obtain ⟨p₀, hp₀⟩ := hU.2.1.nonempty
  obtain ⟨A, hAp₀⟩ := Arxiv240919103H2Proof.exists_mobius_to_infty p₀
  obtain ⟨B₀, hB₀⟩ := Arxiv240919103H2Proof.exists_mobius_to_infty (f p₀)
  have hG : IsCircleDomain ((fun p => A • p) '' U) :=
    Arxiv240919103H2Proof.isCircleDomain_smul A hU
  have hinf : ∞ ∈ (fun p => A • p) '' U := ⟨p₀, hp₀, hAp₀⟩
  have hh0_eq : IsConformalEquivalence (fun p => B₀ • f (A⁻¹ • p))
      ((fun p => A • p) '' U) ((fun p => B₀ • p) '' V) :=
    Arxiv240919103H2Proof.isConformalEquivalence_conj hf A B₀
  have hh0_fix : B₀ • f (A⁻¹ • ∞) = ∞ := by
    calc B₀ • f (A⁻¹ • ∞) = B₀ • f (A⁻¹ • (A • p₀)) := by rw [← hAp₀]
      _ = B₀ • f p₀ := by rw [inv_smul_smul]
      _ = ∞ := hB₀
  obtain ⟨d, c, hd, hbigO⟩ :=
    Arxiv240919103H2Proof.exists_affine_normalization hG.1 hinf hh0_eq hh0_fix
  let S := Arxiv240919103H2Proof.mobAffine d c hd
  let B : Mobius := S * B₀
  have hBV : ((fun p => B • f (A⁻¹ • p)) '' ((fun p => A • p) '' U)) =
      (fun p => B • p) '' V := by
    rcases hf with ⟨_, hf_maps, g, _, hg_maps, _, hfg⟩
    ext w
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨f u, hf_maps hu, by simp [inv_smul_smul]⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨A • g v, ⟨g v, hg_maps hv, rfl⟩, by simp [inv_smul_smul, hfg v hv]⟩
  refine ⟨A, B, hG, hinf, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hBV]
    exact Arxiv240919103H2Proof.isConformalEquivalence_conj hf A B
  · change (S * B₀) • f (A⁻¹ • ∞) = ∞
    rw [mul_smul, hh0_fix]
    exact Arxiv240919103H2Proof.mobAffine_apply_infty d c hd
  · simpa [B, S, mul_smul] using hbigO
  · rw [hBV]
    exact Arxiv240919103H2Proof.isCircleDomain_smul B hV
  · have hfront : frontier ((fun p => A • p) '' U) = (fun p => A • p) '' frontier U :=
      ((Arxiv240919103H2Proof.mobiusHomeo A).image_frontier U).symm
    rw [hfront]
    exact Arxiv240919103H2Proof.isConformallyRemovable_smul A hrem
