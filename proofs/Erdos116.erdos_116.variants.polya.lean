import FormalConjectures.ErdosProblems.«116»
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Pólya's lemniscate inequality (Erdős Problem 116). -/

-- Problem: Erdős Problem 116 — polya
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/116.lean:99 (declaration Erdos116.erdos_116.variants.polya)
-- Credit: @kintonc (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

section PolyaProof

open MeasureTheory Polynomial Pointwise

private lemma real_det_mulLeft (c : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  have h0 : Complex.basisOneI 0 = 1 := by simp [Complex.coe_basisOneI]
  have h1 : Complex.basisOneI 1 = Complex.I := by simp [Complex.coe_basisOneI]
  have hrepr : ∀ v : ℂ, (Complex.basisOneI.repr v) 0 = v.re ∧ (Complex.basisOneI.repr v) 1 = v.im := by
    intro v
    have hv : v = v.re • Complex.basisOneI 0 + v.im • Complex.basisOneI 1 := by
      simp [h0, h1, Complex.real_smul, Complex.re_add_im]
    conv_lhs => rw [hv]
    simp
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI]
  rw [Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply]
  have hmap : ∀ x : ℂ, (((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).toLinearMap) x = x * c :=
    fun _ => rfl
  rw [hmap, hmap, h0, h1, one_mul, (hrepr c).1, (hrepr c).2, (hrepr (Complex.I * c)).1, (hrepr (Complex.I * c)).2]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

private lemma polya_scaled {m : ℕ} (hm : 1 ≤ m)
    (ih : ∀ (q : Polynomial ℂ), q.Monic → q.natDegree = m →
      volume {w : ℂ | ‖q.eval w‖ < 1} ≤ ENNReal.ofReal Real.pi)
    (q : Polynomial ℂ) (hq_monic : q.Monic) (hq_deg : q.natDegree = m)
    {R : ℝ} (hR : 0 < R) :
    volume {w : ℂ | ‖q.eval w‖ < R} ≤ ENNReal.ofReal (Real.pi * R ^ (2 / (m : ℝ))) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
  let c : ℝ := R ^ (1 / (m : ℝ))
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hR _
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hc_pow : c ^ m = R := by
    dsimp [c]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le, one_div_mul_cancel hm_ne, Real.rpow_one]
  have hcc_ne : (c : ℂ)⁻¹ ^ m ≠ 0 := pow_ne_zero m (inv_ne_zero (Complex.ofReal_ne_zero.mpr hc_ne))
  let q_sc : Polynomial ℂ := C ((c : ℂ)⁻¹ ^ m) * q.comp (C (c : ℂ) * X)
  have hcx_deg : (C (c : ℂ) * X).natDegree = 1 :=
    Polynomial.natDegree_C_mul_X (c : ℂ) (Complex.ofReal_ne_zero.mpr hc_ne)
  have hcx_lc : (C (c : ℂ) * X).leadingCoeff = (c : ℂ) :=
    leadingCoeff_C_mul_X (c : ℂ)
  have hcomp_lc : (q.comp (C (c : ℂ) * X)).leadingCoeff = (c : ℂ) ^ m := by
    rw [leadingCoeff_comp (by rw [hcx_deg]; exact one_ne_zero)]
    rw [hq_monic.leadingCoeff, hq_deg, hcx_lc, one_mul]
  have hcomp_deg : (q.comp (C (c : ℂ) * X)).natDegree = m := by
    rw [natDegree_comp, hq_deg, hcx_deg, mul_one]
  have hqsc_monic : q_sc.Monic := by
    rw [Monic, leadingCoeff_mul, leadingCoeff_C, hcomp_lc, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero m (Complex.ofReal_ne_zero.mpr hc_ne))]
  have hqsc_deg : q_sc.natDegree = m := by
    rw [natDegree_C_mul hcc_ne, hcomp_deg]
  have hset : {w : ℂ | ‖q.eval w‖ < R} = c • {u : ℂ | ‖q_sc.eval u‖ < 1} := by
    ext w
    simp only [Set.mem_smul_set_iff_inv_smul_mem₀ hc_ne, Set.mem_ofPred_eq]
    have heval : q_sc.eval (c⁻¹ • w) = (c : ℂ)⁻¹ ^ m * q.eval w := by
      simp only [q_sc, eval_mul, eval_C, eval_comp, eval_X]
      congr 2
      rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hc_ne,
        Complex.ofReal_one, one_mul]
    rw [heval, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc_pos.le,
      inv_pow, hc_pow, inv_mul_lt_iff₀ hR, mul_one]
  rw [hset, Measure.addHaar_smul volume c]
  have h_finrank : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  rw [h_finrank, abs_of_nonneg (sq_nonneg c)]
  calc
    ENNReal.ofReal (c ^ 2) * volume {u : ℂ | ‖q_sc.eval u‖ < 1}
      ≤ ENNReal.ofReal (c ^ 2) * ENNReal.ofReal Real.pi :=
        mul_le_mul_of_nonneg_left (ih q_sc hqsc_monic hqsc_deg) bot_le
    _ = ENNReal.ofReal (Real.pi * R ^ (2 / (m : ℝ))) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg c), mul_comm (c ^ 2)]
        congr 2
        dsimp [c]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le, Nat.cast_ofNat, one_div_mul_eq_div]

private lemma polya_scaled_le {m : ℕ} (hm : 1 ≤ m)
    (ih : ∀ (q : Polynomial ℂ), q.Monic → q.natDegree = m →
      volume {w : ℂ | ‖q.eval w‖ < 1} ≤ ENNReal.ofReal Real.pi)
    (q : Polynomial ℂ) (hq_monic : q.Monic) (hq_deg : q.natDegree = m)
    {R : ℝ} (hR : 0 ≤ R) :
    volume {w : ℂ | ‖q.eval w‖ ≤ R} ≤ ENNReal.ofReal (Real.pi * R ^ (2 / (m : ℝ))) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hle : ∀ k : ℕ, volume {w : ℂ | ‖q.eval w‖ ≤ R} ≤
      ENNReal.ofReal (Real.pi * (R + 1 / ((k : ℝ) + 1)) ^ (2 / (m : ℝ))) := by
    intro k
    have hk : 0 < R + 1 / ((k : ℝ) + 1) := add_pos_of_nonneg_of_pos hR (by positivity)
    refine (measure_mono (fun w hw => ?_)).trans (polya_scaled hm ih q hq_monic hq_deg hk)
    exact lt_of_le_of_lt hw (lt_add_of_pos_right R (by positivity))
  have htend : Filter.Tendsto
      (fun k : ℕ => ENNReal.ofReal (Real.pi * (R + 1 / ((k : ℝ) + 1)) ^ (2 / (m : ℝ))))
      Filter.atTop (nhds (ENNReal.ofReal (Real.pi * R ^ (2 / (m : ℝ))))) := by
    refine ENNReal.continuous_ofReal.continuousAt.tendsto.comp ?_
    refine Filter.Tendsto.const_mul Real.pi ?_
    refine (Real.continuous_rpow_const (show (0 : ℝ) ≤ 2 / (m : ℝ) by positivity)).continuousAt.tendsto.comp ?_
    have h0 : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.add h0
  exact ge_of_tendsto htend (Filter.Eventually.of_forall hle)

private lemma lintegral_deriv_sq_le {n : ℕ} (hn : 2 ≤ n)
    (p : Polynomial ℂ) (hp_monic : p.Monic) (hp_deg : p.natDegree = n) :
    ∫⁻ w in {w : ℂ | ‖p.eval w‖ < 1}, ENNReal.ofReal (‖p.derivative.eval w‖ ^ 2) ∂volume ≤
      ENNReal.ofReal ((n : ℝ) * Real.pi) := by
  let E : Set ℂ := {w : ℂ | ‖p.eval w‖ < 1}
  let S_crit : Set ℂ := {w : ℂ | p.derivative.eval w = 0}
  let U : Set ℂ := E \ S_crit
  have hn_ne : n ≠ 0 := by omega
  have hp_deriv_ne : p.derivative ≠ 0 := by
    intro h0
    have hcoeff : p.derivative.coeff (n - 1) = 0 := by rw [h0, coeff_zero]
    have hnm : n - 1 + 1 = n := by omega
    have hnm_c : ((n - 1 : ℕ) : ℂ) + 1 = (n : ℂ) := by exact_mod_cast hnm
    rw [coeff_derivative, hnm, ← hp_deg, hp_monic.coeff_natDegree, one_mul] at hcoeff
    rw [hp_deg, hnm_c] at hcoeff
    exact absurd hcoeff (Nat.cast_ne_zero.mpr hn_ne)
  have hS_fin : S_crit.Finite := by
    refine (p.derivative.roots.toFinset.finite_toSet).subset fun w hw => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hp_deriv_ne, IsRoot]
    exact hw
  have hS_zero : volume S_crit = 0 := hS_fin.measure_zero volume
  have hU_open : IsOpen U :=
    (isOpen_lt (continuous_norm.comp p.continuous) continuous_const).sdiff
      (isClosed_eq p.derivative.continuous continuous_const)
  have hE_ae : U =ᵐ[volume] E := by
    change ∀ᵐ w ∂volume, (w ∈ U) = (w ∈ E)
    rw [ae_iff]
    refine measure_mono_null (fun w hw => ?_) hS_zero
    simp only [Set.mem_ofPred_eq, eq_iff_iff] at hw
    by_contra hnot
    exact hw ⟨fun h => h.1, fun h => ⟨h, hnot⟩⟩
  rw [← Measure.restrict_congr_set hE_ae]
  by_cases hU_empty : U = ∅
  · rw [hU_empty, Measure.restrict_empty, lintegral_zero_measure]
    exact bot_le
  have h_loc : ∀ w : U, ∃ (e : OpenPartialHomeomorph ℂ ℂ),
      w.1 ∈ e.source ∧ e.source ⊆ U ∧ (∀ z, e z = p.eval z) := by
    intro ⟨w, hw⟩
    have hw_ne : p.derivative.eval w ≠ 0 := hw.2
    let f' : ℂ ≃L[ℝ] ℂ :=
      { toFun := fun z => p.derivative.eval w * z
        map_add' := fun x y => mul_add _ x y
        map_smul' := fun r x => by simp [Complex.real_smul]; ring
        invFun := fun z => (p.derivative.eval w)⁻¹ * z
        left_inv := fun z => by simp [hw_ne]
        right_inv := fun z => by simp [hw_ne]
        continuous_toFun := continuous_const.mul continuous_id
        continuous_invFun := continuous_const.mul continuous_id }
    have hf'_eq : (f' : ℂ →L[ℝ] ℂ) =
        (ContinuousLinearMap.toSpanSingleton ℂ (p.derivative.eval w)).restrictScalars ℝ := by
      ext z
      simp [f', ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
    have hderiv : HasStrictFDerivAt (fun z => p.eval z) (f' : ℂ →L[ℝ] ℂ) w := by
      rw [hf'_eq]
      exact (p.hasStrictDerivAt w).hasStrictFDerivAt.restrictScalars ℝ
    let e0 := hderiv.toOpenPartialHomeomorph (fun z => p.eval z)
    let e := e0.restrOpen U hU_open
    refine ⟨e, ?_, ?_, ?_⟩
    · exact ⟨hderiv.mem_toOpenPartialHomeomorph_source, hw⟩
    · exact fun z hz => hz.2
    · intro z
      rfl
  choose e he_mem he_sub he_fun using h_loc
  obtain ⟨T, hT_count, hT_cov⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun w : U => (e w).source)
      (fun w => (e w).open_source)
  have hT_ne : T.Nonempty := by
    obtain ⟨w0, hw0⟩ := Set.nonempty_iff_ne_empty.mpr hU_empty
    have hmem : w0 ∈ ⋃ w : U, (e w).source := Set.mem_iUnion.mpr ⟨⟨w0, hw0⟩, he_mem ⟨w0, hw0⟩⟩
    rw [← hT_cov] at hmem
    obtain ⟨w1, hw1, _⟩ := Set.mem_iUnion₂.mp hmem
    exact ⟨w1, hw1⟩
  obtain ⟨g, hg_surj⟩ := hT_count.exists_surjective hT_ne
  let B : ℕ → Set ℂ := fun k => (e (g k).1).source
  have hB_open : ∀ k, IsOpen (B k) := fun k => (e (g k).1).open_source
  have hB_cov : ⋃ k, B k = U := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun k => he_sub (g k).1
    · intro z hz
      have hmem : z ∈ ⋃ w : U, (e w).source := Set.mem_iUnion.mpr ⟨⟨z, hz⟩, he_mem ⟨z, hz⟩⟩
      rw [← hT_cov] at hmem
      obtain ⟨w1, hw1, hzw1⟩ := Set.mem_iUnion₂.mp hmem
      obtain ⟨k, hk⟩ := hg_surj ⟨w1, hw1⟩
      exact Set.mem_iUnion.mpr ⟨k, by simpa [B, hk] using hzw1⟩
  let Uk : ℕ → Set ℂ := disjointed B
  have hUk_meas : ∀ k, MeasurableSet (Uk k) :=
    MeasurableSet.disjointed fun k => (hB_open k).measurableSet
  have hUk_disj : Pairwise (Function.onFun Disjoint Uk) := disjoint_disjointed B
  have hUk_cov : ⋃ k, Uk k = U := (iUnion_disjointed).trans hB_cov
  have hUk_sub_B : ∀ k, Uk k ⊆ B k := fun k => disjointed_subset B k
  have hUk_sub_E : ∀ k, Uk k ⊆ E := fun k => (hUk_sub_B k).trans ((he_sub (g k).1).trans Set.sdiff_subset)
  have himg_meas : ∀ k, MeasurableSet ((fun z => p.eval z) '' Uk k) := by
    intro k
    have himg : (fun z => p.eval z) '' Uk k = (e (g k).1).target ∩ (e (g k).1).symm ⁻¹' Uk k := by
      ext u
      constructor
      · rintro ⟨z, hz, rfl⟩
        dsimp only
        rw [← he_fun (g k).1 z]
        have hz_src : z ∈ (e (g k).1).source := hUk_sub_B k hz
        exact ⟨(e (g k).1).map_source hz_src, by simpa [(e (g k).1).left_inv hz_src] using hz⟩
      · rintro ⟨hu_tgt, hu_pre⟩
        refine ⟨(e (g k).1).symm u, hu_pre, ?_⟩
        dsimp only
        rw [← he_fun (g k).1 ((e (g k).1).symm u)]
        exact (e (g k).1).right_inv hu_tgt
    rw [himg]
    have hsub_meas : MeasurableSet (((e (g k).1).target.domRestrict (e (g k).1).symm) ⁻¹' Uk k) :=
      (continuousOn_iff_continuous_domRestrict.mp (e (g k).1).continuousOn_symm).measurable (hUk_meas k)
    have heq_img : (e (g k).1).target ∩ (e (g k).1).symm ⁻¹' Uk k =
        Subtype.val '' (((e (g k).1).target.domRestrict (e (g k).1).symm) ⁻¹' Uk k) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image, Set.domRestrict_apply]
      constructor
      · rintro ⟨hu_tgt, hu_pre⟩
        exact ⟨⟨u, hu_tgt⟩, hu_pre, rfl⟩
      · rintro ⟨⟨v, hv⟩, hv_pre, rfl⟩
        exact ⟨hv, hv_pre⟩
    rw [heq_img]
    exact (MeasurableEmbedding.subtype_coe (e (g k).1).open_target.measurableSet).measurableSet_image.mpr hsub_meas
  have himg_vol : ∀ k, volume ((fun z => p.eval z) '' Uk k) =
      ∫⁻ w in Uk k, ENNReal.ofReal (‖p.derivative.eval w‖ ^ 2) ∂volume := by
    intro k
    have hinj : Set.InjOn (fun z => p.eval z) (Uk k) := by
      intro x hx y hy hxy
      apply (e (g k).1).injOn (hUk_sub_B k hx) (hUk_sub_B k hy)
      simpa only [he_fun (g k).1] using hxy
    have hf' : ∀ x ∈ Uk k, HasFDerivWithinAt (fun z => p.eval z)
        ((ContinuousLinearMap.toSpanSingleton ℂ (p.derivative.eval x)).restrictScalars ℝ) (Uk k) x :=
      fun x _ => ((p.hasStrictDerivAt x).hasStrictFDerivAt.restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
    have hjac := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      (hUk_meas k) hf' hinj (fun _ => (1 : ENNReal))
    simp only [mul_one, setLIntegral_one] at hjac
    rw [hjac]
    refine setLIntegral_congr_fun (hUk_meas k) (fun w _ => ?_)
    rw [real_det_mulLeft, abs_of_nonneg (sq_nonneg _)]
  have hsum_eq : ∫⁻ w in U, ENNReal.ofReal (‖p.derivative.eval w‖ ^ 2) ∂volume =
      ∑' k, ∫⁻ u in Metric.ball (0 : ℂ) 1, ((fun z => p.eval z) '' Uk k).indicator 1 u ∂volume := by
    rw [← hUk_cov, lintegral_iUnion hUk_meas hUk_disj]
    refine tsum_congr fun k => ?_
    have hsub : (fun z => p.eval z) '' Uk k ⊆ Metric.ball (0 : ℂ) 1 := by
      rintro u ⟨w, hw, rfl⟩
      have hwE : ‖p.eval w‖ < 1 := hUk_sub_E k hw
      simpa [Metric.mem_ball, dist_zero_right] using hwE
    rw [← himg_vol k, setLIntegral_indicator (himg_meas k)]
    simp only [Pi.one_apply, setLIntegral_one]
    rw [Set.inter_eq_left.mpr hsub]
  have htsum := lintegral_tsum (μ := volume.restrict (Metric.ball (0 : ℂ) 1))
    (f := fun k u => ((fun z => p.eval z) '' Uk k).indicator (1 : ℂ → ENNReal) u)
    (fun k => (measurable_const.indicator (himg_meas k)).aemeasurable)
  rw [hsum_eq, ← htsum]
  have hpt : ∀ u : ℂ, ∑' k, ((fun z => p.eval z) '' Uk k).indicator (1 : ℂ → ENNReal) u ≤ (n : ENNReal) := by
    intro u
    classical
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F => ?_
    let F' := F.filter fun k => u ∈ (fun z => p.eval z) '' Uk k
    have hsum_F : ∑ k ∈ F, ((fun z => p.eval z) '' Uk k).indicator (1 : ℂ → ENNReal) u =
        (F'.card : ENNReal) := by
      simp only [Set.indicator_apply, Pi.one_apply, ← Finset.sum_filter, F', Finset.sum_const,
        nsmul_eq_mul, mul_one]
    rw [hsum_F]
    norm_cast
    have hex : ∀ k : ℕ, k ∈ F' → ∃ w ∈ Uk k, p.eval w = u := by
      intro k hk
      exact (Finset.mem_filter.mp hk).2
    choose w hw_mem hw_eval using fun k (hk : k ∈ F') => hex k hk
    have hpcu_ne : p - C u ≠ 0 := by
      intro h0
      have hdeg : (p - C u).natDegree = 0 := by rw [h0, natDegree_zero]
      have hdeg2 : (p - C u).natDegree = n := by
        rw [natDegree_sub_C, hp_deg]
      omega
    have hinj_w : Set.InjOn (fun k : F' => w k.1 k.2) Set.univ := by
      rintro ⟨k1, hk1⟩ _ ⟨k2, hk2⟩ _ heq
      by_contra hne
      have hk_ne : k1 ≠ k2 := fun h => hne (Subtype.ext h)
      have hdisj := hUk_disj hk_ne
      dsimp only at heq
      exact Set.disjoint_left.mp hdisj (hw_mem k1 hk1) (heq ▸ hw_mem k2 hk2)
    let S_roots : Finset ℂ := F'.attach.image fun k => w k.1 k.2
    have hcard_eq : S_roots.card = F'.card := by
      rw [Finset.card_image_of_injOn (fun x _ y _ h => hinj_w trivial trivial h), Finset.card_attach]
    rw [← hcard_eq]
    have hsub : S_roots ⊆ (p - C u).roots.toFinset := by
      intro z hz
      obtain ⟨⟨k, hk⟩, _, rfl⟩ := Finset.mem_image.mp hz
      simp only [Multiset.mem_toFinset, mem_roots hpcu_ne, IsRoot, eval_sub, eval_C, sub_eq_zero]
      exact hw_eval k hk
    calc
      S_roots.card ≤ (p - C u).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ (p - C u).roots.card := Multiset.toFinset_card_le _
      _ ≤ (p - C u).natDegree := Polynomial.card_roots' _
      _ = n := by rw [natDegree_sub_C, hp_deg]
  calc
    ∫⁻ u in Metric.ball (0 : ℂ) 1, ∑' k, ((fun z => p.eval z) '' Uk k).indicator 1 u ∂volume
      ≤ ∫⁻ _ in Metric.ball (0 : ℂ) 1, (n : ENNReal) ∂volume := setLIntegral_mono_ae' measurableSet_ball
          (ae_of_all _ fun u _ => hpt u)
    _ = (n : ENNReal) * volume (Metric.ball (0 : ℂ) 1) := by simp
    _ = ENNReal.ofReal ((n : ℝ) * Real.pi) := by
        rw [Complex.volume_ball, ENNReal.ofReal_one, one_pow, one_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast,
          ENNReal.ofReal_eq_coe_nnreal Real.pi_pos.le]
        rfl

private lemma polya_monic (n : ℕ) (hn : 1 ≤ n) :
    ∀ (p : Polynomial ℂ), p.Monic → p.natDegree = n →
      volume {w : ℂ | ‖p.eval w‖ < 1} ≤ ENNReal.ofReal Real.pi := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hp_monic hp_deg
    by_cases hn1 : n = 1
    · subst hn1
      let c0 : ℂ := p.coeff 0
      have hp1 : p.coeff 1 = 1 := by rw [← hp_deg, hp_monic.coeff_natDegree]
      have hp_eq : p = X + C c0 := by
        ext k
        rcases k with _ | _ | k
        · simp [c0]
        · simp [hp1]
        · simp [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < k + 2), coeff_X]
      have hset : {w : ℂ | ‖p.eval w‖ < 1} = Metric.ball (-c0) 1 := by
        ext w
        change ‖p.eval w‖ < 1 ↔ dist w (-c0) < 1
        rw [Complex.dist_eq, sub_neg_eq_add, hp_eq, eval_add, eval_X, eval_C]
      rw [hset, Complex.volume_ball, ENNReal.ofReal_one, one_pow, one_mul]
      exact le_of_eq (ENNReal.ofReal_eq_coe_nnreal Real.pi_pos.le).symm
    have hn2 : 2 ≤ n := by omega
    let m : ℕ := n - 1
    have hm1 : 1 ≤ m := by omega
    have hm_lt : m < n := by omega
    have hm_add : (m : ℝ) + 1 = (n : ℝ) := by
      norm_cast
      omega
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm1
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    let E : Set ℂ := {w : ℂ | ‖p.eval w‖ < 1}
    have hE_meas : MeasurableSet E :=
      (isOpen_lt (continuous_norm.comp p.continuous) continuous_const).measurableSet
    have hE_lt_top : volume E < ⊤ := by
      let C0 : ℝ := ∑ i ∈ Finset.range n, ‖p.coeff i‖
      let R0 : ℝ := max 1 (1 + C0)
      have hsub : E ⊆ Metric.ball (0 : ℂ) R0 := by
        intro w hw
        by_contra hnot
        simp only [Metric.mem_ball, dist_zero_right, not_lt] at hnot
        have hw1 : 1 ≤ ‖w‖ := le_trans (le_max_left 1 (1 + C0)) hnot
        have hwC : 1 + C0 ≤ ‖w‖ := le_trans (le_max_right 1 (1 + C0)) hnot
        have hp_eval : p.eval w = w ^ n + ∑ i ∈ Finset.range n, p.coeff i * w ^ i := by
          rw [eval_eq_sum_range, Finset.sum_range_succ, hp_deg, ← hp_deg,
            hp_monic.coeff_natDegree, one_mul, add_comm]
        have hsum_le : ∑ i ∈ Finset.range n, ‖p.coeff i * w ^ i‖ ≤ C0 * ‖w‖ ^ m := by
          calc
            ∑ i ∈ Finset.range n, ‖p.coeff i * w ^ i‖
              = ∑ i ∈ Finset.range n, ‖p.coeff i‖ * ‖w‖ ^ i := by
                refine Finset.sum_congr rfl fun i _ => by rw [norm_mul, norm_pow]
            _ ≤ ∑ i ∈ Finset.range n, ‖p.coeff i‖ * ‖w‖ ^ m := by
                refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
                exact pow_le_pow_right₀ hw1 (by rw [Finset.mem_range] at hi; omega)
            _ = C0 * ‖w‖ ^ m := by rw [← Finset.sum_mul]
        have htri : 1 ≤ ‖p.eval w‖ := by
          calc
            1 ≤ ‖w‖ ^ m := one_le_pow₀ hw1
            _ = ‖w‖ ^ n - (‖w‖ - 1) * ‖w‖ ^ m := by
                rw [show n = m + 1 by omega, pow_succ']
                ring
            _ ≤ ‖w‖ ^ n - C0 * ‖w‖ ^ m := by
                refine sub_le_sub_left (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (norm_nonneg w) m)) _
            _ ≤ ‖w ^ n‖ - ‖∑ i ∈ Finset.range n, p.coeff i * w ^ i‖ := by
                rw [norm_pow]
                exact sub_le_sub_left ((norm_sum_le _ _).trans hsum_le) _
            _ ≤ ‖w ^ n + ∑ i ∈ Finset.range n, p.coeff i * w ^ i‖ := by
                simpa using norm_sub_norm_le (w ^ n) (-(∑ i ∈ Finset.range n, p.coeff i * w ^ i))
            _ = ‖p.eval w‖ := by rw [hp_eval]
        exact (not_le_of_gt hw) htri
      exact (measure_mono hsub).trans_lt
        (by rw [Complex.volume_ball]; exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.coe_lt_top)
    let V : ℝ := (volume E).toReal
    have hV_nn : 0 ≤ V := ENNReal.toReal_nonneg
    have hV_eq : ENNReal.ofReal V = volume E := ENNReal.ofReal_toReal hE_lt_top.ne
    let q : Polynomial ℂ := C ((n : ℂ)⁻¹) * p.derivative
    have hmn : m + 1 = n := by omega
    have hn_ne : n ≠ 0 := by omega
    have hp_n : p.coeff n = 1 := by rw [← hp_deg, hp_monic.coeff_natDegree]
    have hq_deg : q.natDegree = m := by
      have hn_c : (n : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hn_ne)
      rw [natDegree_C_mul hn_c]
      apply natDegree_eq_of_le_of_coeff_ne_zero
      · exact (natDegree_derivative_le p).trans (by rw [hp_deg])
      · rw [coeff_derivative, hmn, hp_n, one_mul,
          show (m : ℂ) + 1 = (n : ℂ) by exact_mod_cast hmn]
        exact (Nat.cast_ne_zero (R := ℂ)).mpr hn_ne
    have hq_monic : q.Monic := by
      rw [Monic, leadingCoeff, hq_deg, coeff_C_mul, coeff_derivative, hmn, hp_n, one_mul,
        show (m : ℂ) + 1 = (n : ℂ) by exact_mod_cast hmn]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn_ne)
    have h_layer : ∫⁻ w in E, ENNReal.ofReal (‖q.eval w‖ ^ 2) ∂volume =
        ∫⁻ s in Set.Ioi (0 : ℝ), volume (E ∩ {w : ℂ | s < ‖q.eval w‖ ^ 2}) ∂volume := by
      have h_eq := MeasureTheory.lintegral_eq_lintegral_meas_lt (volume.restrict E)
        (ae_of_all _ fun _ => sq_nonneg _)
        ((continuous_norm.comp q.continuous).pow 2).aemeasurable
      dsimp only [Function.comp_apply] at h_eq
      rw [h_eq]
      refine setLIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      rw [Measure.restrict_apply]
      · rw [Set.inter_comm]
      · exact (isOpen_lt continuous_const ((continuous_norm.comp q.continuous).pow 2)).measurableSet
    have h_s_lb : ∀ s : ℝ, 0 < s →
        ENNReal.ofReal (V - Real.pi * s ^ (1 / (m : ℝ))) ≤
          volume (E ∩ {w : ℂ | s < ‖q.eval w‖ ^ 2}) := by
      intro s hs
      have hcov : E ⊆ (E ∩ {w : ℂ | s < ‖q.eval w‖ ^ 2}) ∪ {w : ℂ | ‖q.eval w‖ ≤ Real.sqrt s} := by
        intro w hw
        by_cases hlt : s < ‖q.eval w‖ ^ 2
        · exact Or.inl ⟨hw, hlt⟩
        · refine Or.inr ?_
          rw [not_lt] at hlt
          exact Real.le_sqrt_of_sq_le hlt
      have hmeas_add : volume E ≤
          volume (E ∩ {w : ℂ | s < ‖q.eval w‖ ^ 2}) + volume {w : ℂ | ‖q.eval w‖ ≤ Real.sqrt s} :=
        (measure_mono hcov).trans (measure_union_le _ _)
      have hq_le : volume {w : ℂ | ‖q.eval w‖ ≤ Real.sqrt s} ≤
          ENNReal.ofReal (Real.pi * s ^ (1 / (m : ℝ))) := by
        have hsqrt := polya_scaled_le hm1 (ih m hm_lt hm1) q hq_monic hq_deg (Real.sqrt_nonneg s)
        refine hsqrt.trans_eq ?_
        congr 2
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]
        congr 1
        ring
      rw [ENNReal.ofReal_sub _ (mul_nonneg Real.pi_pos.le (Real.rpow_nonneg hs.le _)), hV_eq]
      exact tsub_le_iff_right.mpr (hmeas_add.trans (add_le_add_right hq_le _))
    let S : ℝ := (V / Real.pi) ^ m
    have hS_nn : 0 ≤ S := pow_nonneg (div_nonneg hV_nn Real.pi_pos.le) m
    let f : ℝ → ℝ := fun s => V - Real.pi * s ^ (1 / (m : ℝ))
    have hf_cont : Continuous f :=
      continuous_const.sub (continuous_const.mul (Real.continuous_rpow_const (by positivity)))
    have hf_nn : ∀ s ∈ Set.Ioc (0 : ℝ) S, 0 ≤ f s := by
      intro s ⟨hs0, hsS⟩
      dsimp [f]
      have hpow : s ^ (1 / (m : ℝ)) ≤ V / Real.pi := by
        calc
          s ^ (1 / (m : ℝ)) ≤ S ^ (1 / (m : ℝ)) :=
            Real.rpow_le_rpow hs0.le hsS (by positivity)
          _ = V / Real.pi := by
            dsimp [S]
            rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hV_nn Real.pi_pos.le),
              mul_one_div_cancel hm_pos.ne', Real.rpow_one]
      linarith [mul_le_mul_of_nonneg_left hpow Real.pi_pos.le,
        mul_div_cancel₀ V Real.pi_pos.ne']
    have h_int_lb : ENNReal.ofReal (V ^ n / ((n : ℝ) * Real.pi ^ m)) ≤
        ∫⁻ w in E, ENNReal.ofReal (‖q.eval w‖ ^ 2) ∂volume := by
      have hint_val : ∫ s in (0 : ℝ)..S, f s = V ^ n / ((n : ℝ) * Real.pi ^ m) := by
        have h1 : ∫ _ in (0 : ℝ)..S, V = V * S := by simp [mul_comm]
        have h2 : ∫ s in (0 : ℝ)..S, Real.pi * s ^ (1 / (m : ℝ)) =
            Real.pi * (S ^ (1 / (m : ℝ) + 1) / (1 / (m : ℝ) + 1)) := by
          have hexp_pos : (0 : ℝ) < 1 / (m : ℝ) + 1 := by positivity
          have hexp_gt : (-1 : ℝ) < 1 / (m : ℝ) := by linarith
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hexp_gt)]
          rw [Real.zero_rpow hexp_pos.ne', sub_zero]
        have hsub : ∫ s in (0 : ℝ)..S, (V - Real.pi * s ^ (1 / (m : ℝ))) =
            (∫ _ in (0 : ℝ)..S, V) - ∫ s in (0 : ℝ)..S, Real.pi * s ^ (1 / (m : ℝ)) :=
          intervalIntegral.integral_sub intervalIntegrable_const
            ((continuous_const.mul (Real.continuous_rpow_const (by positivity))).intervalIntegrable 0 S)
        change ∫ s in (0 : ℝ)..S, (V - Real.pi * s ^ (1 / (m : ℝ))) = _
        rw [hsub, h1, h2]
        have hS_pow : S ^ (1 / (m : ℝ) + 1) = S * (V / Real.pi) := by
          rw [Real.rpow_add' hS_nn (by positivity), Real.rpow_one]
          dsimp [S]
          rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hV_nn Real.pi_pos.le),
            mul_one_div_cancel hm_pos.ne', Real.rpow_one, mul_comm]
        rw [hS_pow]
        have hexp : (1 / (m : ℝ) + 1) = (n : ℝ) / (m : ℝ) := by
          field_simp
          linarith
        rw [hexp]
        have hVS : V * S = V ^ n / Real.pi ^ m := by
          dsimp [S]
          rw [div_pow, show n = m + 1 by omega, pow_succ']
          ring
        calc
          V * S - Real.pi * (S * (V / Real.pi) / ((n : ℝ) / (m : ℝ)))
            = V * S * (1 - (m : ℝ) / (n : ℝ)) := by
                field_simp [Real.pi_pos.ne', hn_pos.ne', hm_pos.ne']
          _ = V * S / (n : ℝ) := by
                have h1mn : 1 - (m : ℝ) / (n : ℝ) = 1 / (n : ℝ) := by
                  field_simp
                  linarith
                rw [h1mn, mul_one_div]
          _ = V ^ n / ((n : ℝ) * Real.pi ^ m) := by
                rw [hVS, div_div, mul_comm (Real.pi ^ m) (n : ℝ)]
      rw [← hint_val, intervalIntegral.integral_of_le hS_nn]
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_cont.integrableOn_Ioc
        (ae_restrict_of_forall_mem measurableSet_Ioc hf_nn)]
      rw [h_layer]
      refine le_trans ?_ (lintegral_mono_set (fun _ hx => hx.1 : Set.Ioc 0 S ⊆ Set.Ioi 0))
      exact setLIntegral_mono_ae' measurableSet_Ioc
        (ae_of_all _ fun s hs => h_s_lb s hs.1)
    have h_comb : ENNReal.ofReal ((n : ℝ) * V ^ n / Real.pi ^ m) ≤
        ENNReal.ofReal ((n : ℝ) * Real.pi) := by
      have h_mul : ∫⁻ w in E, ENNReal.ofReal (‖p.derivative.eval w‖ ^ 2) ∂volume =
          ENNReal.ofReal ((n : ℝ) ^ 2) * ∫⁻ w in E, ENNReal.ofReal (‖q.eval w‖ ^ 2) ∂volume := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun hE_meas fun w _ => ?_
        rw [← ENNReal.ofReal_mul (sq_nonneg (n : ℝ))]
        congr 1
        have hq_eval : q.eval w = (n : ℂ)⁻¹ * p.derivative.eval w := by
          simp [q]
        rw [hq_eval, norm_mul, norm_inv, Complex.norm_natCast, mul_pow, inv_pow]
        field_simp [hn_pos.ne']
      calc
        ENNReal.ofReal ((n : ℝ) * V ^ n / Real.pi ^ m)
          = ENNReal.ofReal ((n : ℝ) ^ 2) * ENNReal.ofReal (V ^ n / ((n : ℝ) * Real.pi ^ m)) := by
            rw [← ENNReal.ofReal_mul (sq_nonneg (n : ℝ))]
            congr 1
            field_simp [hn_pos.ne']
        _ ≤ ENNReal.ofReal ((n : ℝ) ^ 2) * ∫⁻ w in E, ENNReal.ofReal (‖q.eval w‖ ^ 2) ∂volume :=
            mul_le_mul_of_nonneg_left h_int_lb bot_le
        _ = ∫⁻ w in E, ENNReal.ofReal (‖p.derivative.eval w‖ ^ 2) ∂volume := h_mul.symm
        _ ≤ ENNReal.ofReal ((n : ℝ) * Real.pi) :=
            lintegral_deriv_sq_le hn2 p hp_monic hp_deg
    have h_real : (n : ℝ) * V ^ n / Real.pi ^ m ≤ (n : ℝ) * Real.pi :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hn_pos.le Real.pi_pos.le)).mp h_comb
    have h_pow : V ^ n ≤ Real.pi ^ n := by
      have hpi_m : 0 < Real.pi ^ m := pow_pos Real.pi_pos m
      have h1 : (n : ℝ) * V ^ n ≤ (n : ℝ) * (Real.pi ^ m * Real.pi) := by
        rw [← mul_assoc, mul_comm ((n : ℝ) * Real.pi ^ m) Real.pi]
        have h2 := (div_le_iff₀ hpi_m).mp h_real
        linarith
      rw [← pow_succ, hmn] at h1
      exact le_of_mul_le_mul_left h1 hn_pos
    have hV_le : V ≤ Real.pi :=
      le_of_pow_le_pow_left₀ (by omega) Real.pi_pos.le h_pow
    rw [← hV_eq]
    exact ENNReal.ofReal_le_ofReal hV_le

end PolyaProof

theorem OMA.solution : type_of% @Erdos116.erdos_116.variants.polya := by
  intro n z
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hset : {w : ℂ | ‖∏ i : Fin 0, (w - z i)‖ < 1} = ∅ := by
      ext w
      simp
    rw [hset, MeasureTheory.measure_empty]
    exact bot_le
  · let p : Polynomial ℂ := ∏ i : Fin n, (Polynomial.X - Polynomial.C (z i))
    have hp_monic : p.Monic :=
      Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (z i)
    have hp_deg : p.natDegree = n := by
      rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (z i)]
      simp
    have heval : ∀ w : ℂ, p.eval w = ∏ i : Fin n, (w - z i) := by
      intro w
      simp [p, Polynomial.eval_prod]
    simp_rw [← heval]
    exact polya_monic n hn p hp_monic hp_deg
