import OMAReductions.R_Erdos1038_erdos_1038_parts_ii_R1_H2_R1
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.Compact

/-! Transport the tail witness for Tao's logarithmic-potential proof.
First keep a compact set of sufficient measure. Its cumulative
measure is 1-Lipschitz and the inverse quantile realizes every
positive required mass at a point in the compact set. -/

open Set MeasureTheory
open scoped ENNReal

namespace OMA.TaoQuantile

noncomputable def cumulative (K : Set ℝ) (x : ℝ) : ℝ :=
  (volume (K ∩ Iic x)).toReal

private theorem finite_part {K : Set ℝ} (hK : IsCompact K) (S : Set ℝ) :
    volume (K ∩ S) ≠ ∞ :=
  ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono inter_subset_left)

theorem cumulative_mono {K : Set ℝ} (hK : IsCompact K) : Monotone (cumulative K) := by
  intro x y hxy
  exact ENNReal.toReal_mono (finite_part hK _) (measure_mono (inter_subset_inter_right _ (Iic_subset_Iic.2 hxy)))

theorem cumulative_difference {K : Set ℝ} (hK : IsCompact K) {x y : ℝ} (hxy : x ≤ y) :
    cumulative K y - cumulative K x ≤ y-x := by
  have hsplit : K ∩ Iic y = (K ∩ Iic x) ∪ (K ∩ Ioc x y) := by
    ext t
    simp only [mem_inter_iff,mem_Iic,mem_union,mem_Ioc]
    constructor
    · intro h
      by_cases ht : t ≤ x
      · exact Or.inl ⟨h.1,ht⟩
      · exact Or.inr ⟨h.1,lt_of_not_ge ht,h.2⟩
    · rintro (h|h)
      · exact ⟨h.1,h.2.trans hxy⟩
      · exact ⟨h.1,h.2.2⟩
  have hdis : Disjoint (K ∩ Iic x) (K ∩ Ioc x y) := by
    apply Set.disjoint_left.2
    intro t ht ht'
    exact ht'.2.1.not_ge ht.2
  have hbound : (volume (K ∩ Ioc x y)).toReal ≤ y-x := by
    have hmono := measure_mono (μ := volume) (inter_subset_right : K ∩ Ioc x y ⊆ Ioc x y)
    rw [Real.volume_Ioc] at hmono
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmono
    rwa [ENNReal.toReal_ofReal (sub_nonneg.2 hxy)] at h
  unfold cumulative
  rw [hsplit,measure_union hdis (hK.isClosed.measurableSet.inter measurableSet_Ioc),
    ENNReal.toReal_add (finite_part hK _) (finite_part hK _)]
  linarith only [hbound]

theorem cumulative_lipschitz {K : Set ℝ} (hK : IsCompact K) :
    LipschitzWith 1 (cumulative K) := by
  apply lipschitzWith_iff_dist_le_mul.2
  intro x y
  simp only [NNReal.coe_one,one_mul,Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.2 (cumulative_mono hK hxy)),abs_of_nonpos (sub_nonpos.2 hxy),
      neg_sub,neg_sub]
    exact cumulative_difference hK hxy
  · rw [abs_of_nonneg (sub_nonneg.2 (cumulative_mono hK hyx)),abs_of_nonneg (sub_nonneg.2 hyx)]
    exact cumulative_difference hK hyx

theorem cumulative_left {K : Set ℝ} {a L : ℝ} (hKa : K ⊆ Icc a L) : cumulative K a=0 := by
  have hsub : K ∩ Iic a ⊆ {a} := by
    intro x hx
    exact le_antisymm hx.2 (hKa hx.1).1
  have h : volume (K ∩ Iic a) = 0 := by
    apply le_antisymm _ (by simp)
    exact (measure_mono hsub).trans (by simp)
  simp [cumulative,h]

theorem cumulative_right {K : Set ℝ} {a L : ℝ} (hKa : K ⊆ Icc a L) :
    cumulative K L = (volume K).toReal := by
  have hz : K ⊆ Iic L := fun x hx => (hKa hx).2
  rw [cumulative, inter_eq_left.2 hz]

set_option maxHeartbeats 900000 in
theorem transport {K : Set ℝ} (hK : IsCompact K) {a L m : ℝ} (ha : a ≤ L)
    (hsub : K ⊆ Icc a L) (_hm : 0 ≤ m) (hMass : m ≤ (volume K).toReal) :
    ∃ g : ℝ → ℝ, Measurable g ∧
      ∀ y ∈ Icc 0 m,
        g y ∈ Icc a L ∧ cumulative K (g y) = y ∧ (0 < y → g y ∈ K) := by
  let c (y : ℝ) := min (max y 0) m
  let T (y : ℝ) := Icc a L ∩ {x | c y ≤ cumulative K x}
  let g (y : ℝ) := sInf (T y)
  have hclamp (y : ℝ) (hy : y ∈ Icc 0 m) : c y=y := by
    simp only [c,max_eq_left hy.1,min_eq_left hy.2]
  have hleast (y : ℝ) : IsLeast (T y) (g y) := by
    have hc : IsClosed {x : ℝ | c y ≤ cumulative K x} :=
      isClosed_le continuous_const (cumulative_lipschitz hK).continuous
    have hcomp : IsCompact (T y) := isCompact_Icc.inter_right hc
    have hL : L ∈ T y := by
      refine ⟨⟨ha,le_rfl⟩,?_⟩
      change c y ≤ cumulative K L
      rw [cumulative_right hsub]
      exact (min_le_right ..).trans hMass
    exact hcomp.isLeast_sInf ⟨L,hL⟩
  have hg : Monotone g := by
    intro x y hxy
    have hcy : c x ≤ c y := min_le_min (max_le_max_right _ hxy) le_rfl
    exact (hleast x).2 ⟨(hleast y).1.1,hcy.trans (hleast y).1.2⟩
  refine ⟨g,hg.measurable,?_⟩
  intro y hy
  have hmem := (hleast y).1
  have hr := hmem.1
  have ht : y ≤ cumulative K (g y) := by
    have he : c y ≤ cumulative K (g y) := hmem.2
    rwa [hclamp y hy] at he
  have heq : cumulative K (g y) = y := by
    apply le_antisymm _ ht
    by_contra! h
    have hct : ContinuousOn (cumulative K) (Icc a (g y)) :=
      (cumulative_lipschitz hK).continuous.continuousOn
    have hy' : y ∈ Icc (cumulative K a) (cumulative K (g y)) := by
      rw [cumulative_left hsub]
      exact ⟨hy.1,h.le⟩
    obtain ⟨x,hx,hEx⟩ := intermediate_value_Icc hr.1 hct hy'
    have hxg : g y ≤ x := by
      apply (hleast y).2
      refine ⟨⟨hx.1,hx.2.trans hr.2⟩,?_⟩
      change c y ≤ cumulative K x
      rw [hclamp y hy,hEx]
    have hxEq : x=g y := hx.2.antisymm hxg
    exact h.ne (hxEq ▸ hEx).symm
  refine ⟨hr,heq,?_⟩
  intro hypos
  by_contra hnot
  have hga : a < g y := by
    apply lt_of_le_of_ne hr.1
    intro he
    have hh := cumulative_left hsub
    rw [he,heq] at hh
    exact hypos.ne' hh
  have hope : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  obtain ⟨δ,hδ,hBall⟩ := Metric.isOpen_iff.1 hope (g y) hnot
  let x := g y - min (δ/2) ((g y-a)/2)
  have hxg : x < g y := by
    dsimp only [x]
    exact sub_lt_self _ (lt_min (by linarith only [hδ]) (by linarith only [hga]))
  have hxa : a ≤ x := by
    have hh := min_le_right (δ/2) ((g y-a)/2)
    dsimp only [x]
    linarith only [hh,hga]
  have hsame : K ∩ Iic (g y) = K ∩ Iic x := by
    apply le_antisymm _ (inter_subset_inter_right _ (Iic_subset_Iic.2 hxg.le))
    intro t ht
    refine ⟨ht.1,?_⟩
    change t ≤ x
    by_contra! h
    have hdist : t ∈ Metric.ball (g y) δ := by
      rw [Metric.mem_ball,Real.dist_eq,abs_of_nonpos (sub_nonpos.2 ht.2)]
      have hh := min_le_left (δ/2) ((g y-a)/2)
      dsimp only [x] at h
      linarith only [h,hδ,hh]
    exact hBall hdist ht.1
  have hcum : cumulative K x = y := by
    unfold cumulative at heq ⊢
    rwa [hsame] at heq
  have hmemb : x ∈ T y := by
    refine ⟨⟨hxa,hxg.le.trans hr.2⟩,?_⟩
    change c y ≤ cumulative K x
    rw [hclamp y hy,hcum]
  exact hxg.not_ge ((hleast y).2 hmemb)

end OMA.TaoQuantile


namespace OMA.TaoCompact

private theorem finite_of_bounded {E : Set ℝ} (hE : E ⊆ Ioo (-2 : ℝ) 2) : volume E ≠ ∞ := by
  apply ne_top_of_le_ne_top _ (measure_mono hE)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

theorem compact_left (E : Set ℝ) (hE : IsOpen E) (hbox : E ⊆ Ioo (-2 : ℝ) 2)
    (hvol : ENNReal.ofReal (2*Real.sqrt 2) < volume E)
    (hfar : ∃ x ∈ E, (1.7624 : ℝ) < x) :
    ∃ p ∈ E, (1.7624 : ℝ) < p ∧ p < 2 ∧
      ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Icc (p-1) 4 ∧
        2*Real.sqrt 2-(p-1) < (volume K).toReal ∧
        ∀ z ∈ K, p-z ∈ E := by
  obtain ⟨x,hx,hx'⟩ := hfar
  have hne : E.Nonempty := ⟨x,hx⟩
  have hbd : BddAbove E := ⟨2,fun y hy => (hbox hy).2.le⟩
  let M := sSup E
  have hM (x : ℝ) (hx : x ∈ E) : x ≤ M := le_csSup hbd hx
  have hM₀ : (1.7624 : ℝ) < M := hx'.trans_le (hM x hx)
  have hδ : 2*Real.sqrt 2 < (volume E).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (finite_of_bounded hbox)).1 hvol
  let δ := (volume E).toReal-2*Real.sqrt 2
  have hd : 0 < δ := sub_pos.2 hδ
  have hM₁ : max (1.7624 : ℝ) (M-δ/2) < M := max_lt hM₀ (by linarith only [hd])
  obtain ⟨p,hp,hp'⟩ := exists_lt_of_lt_csSup hne hM₁
  have hpa := lt_of_le_of_lt (le_max_left (1.7624 : ℝ) (M-δ/2)) hp'
  have hpx := lt_of_le_of_lt (le_max_right (1.7624 : ℝ) (M-δ/2)) hp'
  have hpb := (hbox hp).2
  let F := E ∩ Iic 1
  have hsub : E ⊆ F ∪ Ioc 1 M := by
    intro y hy
    by_cases h : y ≤ 1
    · exact Or.inl ⟨hy,h⟩
    · exact Or.inr ⟨lt_of_not_ge h,hM y hy⟩
  have hvF : volume F ≠ ∞ := finite_of_bounded (fun x hx => hbox hx.1)
  have hvM : volume (Ioc 1 M) ≠ ∞ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hFplus : (volume E).toReal ≤ (volume F).toReal + (M-1) := by
    have hh := (measure_mono (μ := volume) hsub).trans (measure_union_le F (Ioc 1 M))
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hvF,hvM⟩) hh
    rw [ENNReal.toReal_add hvF hvM, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith only [hM₀] : 0 ≤ M-1)] at h
    exact h
  let ℓ := 2*Real.sqrt 2-(p-1)
  have hℓ : 0 ≤ ℓ := by
    have hs : (1 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ),
        mul_nonneg (by linarith only [Real.sqrt_nonneg (2 : ℝ)] : 0 ≤ Real.sqrt 2 + 1)
          (by positivity : 0 ≤ Real.sqrt 2)]
    dsimp only [ℓ]
    linarith only [hs,hpb]
  have hL : ℓ < (volume F).toReal := by
    dsimp only [ℓ,δ] at *
    linarith only [hpx,hFplus,hδ]
  obtain ⟨K₀,hKF,hK,hvolK⟩ := (hE.measurableSet.inter measurableSet_Iic).exists_lt_isCompact
    ((ENNReal.ofReal_lt_iff_lt_toReal hℓ hvF).2 hL)
  let f (x : ℝ) := p-x
  let K := f '' K₀
  have hf : Continuous f := continuous_const.sub continuous_id
  have hK' : IsCompact K := hK.image hf
  have hmp : MeasurePreserving f (volume : Measure ℝ) volume := by
    have hn : MeasurePreserving (fun y : ℝ => -y) (volume : Measure ℝ) volume :=
      ⟨measurable_neg, Measure.map_neg_eq_self _⟩
    have hp := (measurePreserving_add_left (volume : Measure ℝ) p).comp hn
    change MeasurePreserving (fun x : ℝ => p + -x) volume volume at hp
    simpa only [f,sub_eq_add_neg] using hp
  have hpre : f ⁻¹' K = K₀ := by
    apply Set.preimage_image_eq
    intro x y h
    dsimp only [f] at h
    linarith only [h]
  have hvol_eq : volume K=volume K₀ := by
    have hh := hmp.measure_preimage hK'.isClosed.measurableSet.nullMeasurableSet
    rwa [hpre,eq_comm] at hh
  refine ⟨p,hp,hpa,hpb,K,hK',?_,?_,?_⟩
  · rintro z ⟨y,hy,rfl⟩
    have h := hKF hy
    have hy₁ : y ≤ 1 := h.2
    have hy₂ := (hbox h.1).1
    change p-1 ≤ p-y ∧ p-y ≤ 4
    constructor <;> linarith only [hy₁,hy₂,hpb]
  · rw [hvol_eq]
    exact (ENNReal.ofReal_lt_iff_lt_toReal hℓ hK.measure_lt_top.ne).1 hvolK
  · rintro z ⟨y,hy,rfl⟩
    change p-(p-y) ∈ E
    rw [sub_sub_cancel]
    exact (hKF hy).1

end OMA.TaoCompact

namespace OMA.TaoNormalize

noncomputable def logDistance (t x : ℝ) : ℝ := Real.log |x-t|

theorem logDistance_measurable (t : ℝ) : Measurable (logDistance t) :=
  Real.measurable_log.comp (measurable_id.sub measurable_const).abs

set_option maxHeartbeats 850000 in
theorem normalize
    (E : Set ℝ) (hE : MeasurableSet E) (hbox : E ⊆ Ioo (-2 : ℝ) 2)
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0) (φ : ℝ → ℝ)
    (hφ : Measurable φ) (himg : ∀ᵐ s ∂ν, φ s ∈ E)
    (hseed : ∀ t ∈ Icc (-1 : ℝ) 1, ∃ τ : ℝ,
      ν {τ} = 0 ∧ Integrable (logDistance τ) ν ∧
      0 < ∫ x, logDistance τ x ∂ν ∧ (∀ᵐ s ∂ν, |s-τ| ≤ |φ s-t|)) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ Eᶜ = 0 ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, μ {t}=0 ∧
        Integrable (logDistance t) μ ∧ 0 < ∫ x, logDistance t x ∂μ := by
  let μ₀ := ν.map φ
  let c := (ν univ)⁻¹
  let μ := c • μ₀
  have h0 : ν univ ≠ 0 := fun h => hν (Measure.measure_univ_eq_zero.1 h)
  have ht : ν univ ≠ ∞ := measure_ne_top _ _
  have hc : c ≠ ∞ := ENNReal.inv_ne_top.2 h0
  have hc₀ : 0 < c.toReal := ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 ht) hc
  have hprob : IsProbabilityMeasure μ := by
    constructor
    unfold μ μ₀
    rw [Measure.smul_apply,Measure.map_apply hφ MeasurableSet.univ,preimage_univ]
    exact ENNReal.inv_mul_cancel h0 ht
  have hmass : μ Eᶜ=0 := by
    unfold μ μ₀
    rw [Measure.smul_apply,Measure.map_apply hφ hE.compl]
    have hnull : ν (φ ⁻¹' Eᶜ)=0 := ae_iff.1 himg
    rw [hnull]
    simp
  refine ⟨μ,hprob,hmass,?_⟩
  intro t ht'
  obtain ⟨τ,hτ,hτi,hτp,hineq⟩ := hseed t ht'
  have hne : ∀ᵐ s ∂ν, s≠τ := by
    rw [ae_iff]
    have he : {s : ℝ | ¬s ≠ τ} = {τ} := by ext s; simp
    rwa [he]
  have hA : ∀ᵐ s ∂ν, 0 < |φ s-t| ∧ logDistance τ s ≤ logDistance t (φ s) := by
    filter_upwards [hne,hineq] with s hs hin
    have hp : 0 < |s-τ| := abs_pos.2 (sub_ne_zero.2 hs)
    exact ⟨hp.trans_le hin,Real.log_le_log hp hin⟩
  have hn : μ {t}=0 := by
    unfold μ μ₀
    rw [Measure.smul_apply,Measure.map_apply hφ (measurableSet_singleton _)]
    have hae : ∀ᵐ s ∂ν, s ∉ φ ⁻¹' {t} := by
      filter_upwards [hA] with x hx hx'
      have he : φ x=t := hx'
      rw [he,sub_self,abs_zero] at hx
      exact hx.1.false
    have hnull : ν (φ ⁻¹' {t}) = 0 := by
      simpa only [not_not,Set.ofPred_mem_eq] using ae_iff.1 hae
    rw [hnull]
    simp
  have hB : ∀ᵐ s ∂ν, |φ s-t| ≤ 3 := by
    filter_upwards [himg] with s hs
    have hb := hbox hs
    apply abs_le.2
    constructor <;> linarith only [hb.1,hb.2,ht'.1,ht'.2]
  have hupper : ∀ᵐ s ∂ν, logDistance t (φ s) ≤ Real.log 3 := by
    filter_upwards [hA,hB] with s hA hB
    exact Real.log_le_log hA.1 hB
  have hdom : ∀ᵐ s ∂ν, ‖logDistance t (φ s)‖ ≤ |logDistance τ s| + Real.log 3 := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)
    filter_upwards [hA,hupper] with s hl hu
    rw [Real.norm_eq_abs]
    apply abs_le.2
    constructor
    · linarith only [hl.2,hlog,neg_abs_le (logDistance τ s)]
    · linarith only [hu,abs_nonneg (logDistance τ s)]
  have hbd : Integrable (fun s => |logDistance τ s| + Real.log 3) ν :=
    hτi.abs.add (integrable_const _)
  have hcomp : Integrable (logDistance t ∘ φ) ν :=
    hbd.mono' ((logDistance_measurable t).comp hφ).aestronglyMeasurable hdom
  have hμi : Integrable (logDistance t) μ₀ :=
    (integrable_map_measure (logDistance_measurable t).aestronglyMeasurable hφ.aemeasurable).2 hcomp
  refine ⟨hn,hμi.smul_measure hc,?_⟩
  have hmono : (∫ s, logDistance τ s ∂ν) ≤ ∫ s, logDistance t (φ s) ∂ν :=
    integral_mono_ae hτi hcomp (hA.mono (fun s hs => hs.2))
  have hpositive := lt_of_lt_of_le hτp hmono
  unfold μ μ₀
  rw [integral_smul_measure,integral_map hφ.aemeasurable (logDistance_measurable t).aestronglyMeasurable]
  exact mul_pos hc₀ hpositive

end OMA.TaoNormalize


namespace OMA.TaoTailTransport

open TaoQuantile TaoCompact TaoNormalize

set_option maxHeartbeats 1600000 in
theorem transfer (E : Set ℝ) (hE : IsOpen E) (hbox : E ⊆ Ioo (-2 : ℝ) 2)
    (hvol : ENNReal.ofReal (2 * Real.sqrt 2) < volume E)
    (hfar : ∃ x ∈ E, (1.7624 : ℝ) < |x|) :
    ∃ a : ℝ, 0.7624 < a ∧ a ≤ 1 ∧
    ∀ ν : Measure ℝ, IsFiniteMeasure ν → ν ≠ 0 → ν ({0} ∪ Icc a (2 * Real.sqrt 2))ᶜ = 0 →
    (∀ t ∈ Icc a (a + 2), ν {t} = 0 ∧
      Integrable (fun s => Real.log |s - t|) ν ∧
      0 < ∫ s, Real.log |s - t| ∂ν) →
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ Eᶜ = 0 ∧
    ∀ t ∈ Icc (-1 : ℝ) 1, μ {t} = 0 ∧
      Integrable (fun x => Real.log |x - t|) μ ∧
      0 < ∫ x, Real.log |x - t| ∂μ := by
  obtain ⟨x,hx,hxa⟩ := hfar
  let ε := if 0 ≤ x then (1 : ℝ) else -1
  have heps : ε=1 ∨ ε= -1 := by unfold ε; split_ifs <;> simp
  let F := (fun y : ℝ => ε*y) ⁻¹' E
  have hFopen : IsOpen F := hE.preimage (continuous_const.mul continuous_id)
  have hFbox : F ⊆ Ioo (-2 : ℝ) 2 := by
    intro y hy
    have hh : ε*y ∈ Ioo (-2 : ℝ) 2 := hbox hy
    rcases heps with h | h
    · simpa only [h,one_mul] using hh
    · rw [h,neg_one_mul] at hh
      exact ⟨by linarith only [hh.2],by linarith only [hh.1]⟩
  have hFvol : volume F = volume E := by
    rcases heps with h | h
    · simp [F,h]
    · change volume ((fun y : ℝ => ε*y) ⁻¹' E)=volume E
      simp only [h,neg_one_mul]
      have hmap := Measure.map_neg_eq_self (volume : Measure ℝ)
      rw [← Measure.map_apply measurable_neg hE.measurableSet, hmap]
  have hFx : |x| ∈ F := by
    change ε*|x| ∈ E
    unfold ε
    by_cases hp : 0 ≤ x
    · rwa [if_pos hp,abs_of_nonneg hp,one_mul]
    · rwa [if_neg hp,abs_of_neg (lt_of_not_ge hp),neg_one_mul,neg_neg]
  obtain ⟨p,hp,hp₁,hp₂,K,hK,hKsub,hKm,hpK⟩ :=
    compact_left F hFopen hFbox (hFvol.symm ▸ hvol) ⟨_,hFx,hxa⟩
  let a := p-1
  let m := 2*Real.sqrt 2-a
  have ha₁ : (0.7624 : ℝ) < a := by dsimp only [a]; linarith only [hp₁]
  have ha₂ : a ≤ 1 := by dsimp only [a]; linarith only [hp₂]
  have ha₀ : 0 < a := by linarith only [ha₁]
  have hm : 0 ≤ m := by
    have hs : 1 ≤ Real.sqrt 2 := by
      nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    dsimp only [m]
    linarith only [ha₂,hs]
  obtain ⟨g,hg,hgl⟩ := transport hK (show a ≤ 4 by linarith only [ha₂]) hKsub hm hKm.le
  refine ⟨a,ha₁,ha₂,?_⟩
  intro ν hνfin hν hSupport hνpot
  letI : IsFiniteMeasure ν := hνfin
  let φ (s : ℝ) : ℝ := if s=0 then ε*p else ε*(p - g (s-a))
  have hφ : Measurable φ := by
    apply Measurable.ite (measurableSet_singleton (0 : ℝ))
    · exact measurable_const
    · exact measurable_const.mul (measurable_const.sub (hg.comp (measurable_id.sub measurable_const)))
  have hνa : ν {a}=0 := (hνpot a ⟨le_rfl,by linarith⟩).1
  have hSupport₁ : ∀ᵐ s ∂ν, s ∈ ({0} ∪ Icc a (2 * Real.sqrt 2)) := ae_iff.2 hSupport
  have hSupport₂ : ∀ᵐ s ∂ν, s ≠ a := by
    rw [ae_iff]
    have he : {s : ℝ | ¬s ≠ a} = {a} := by ext s; simp
    rwa [he]
  have hSupport' : ∀ᵐ s ∂ν, s=0 ∨ s∈Ioc a (2 * Real.sqrt 2) := by
    filter_upwards [hSupport₁,hSupport₂] with s hs hne
    rcases hs with h | h
    · exact Or.inl h
    · exact Or.inr ⟨lt_of_le_of_ne h.1 hne.symm,h.2⟩
  have hsRange (s : ℝ) (hs : s∈Ioc a (2 * Real.sqrt 2)) : s-a∈Icc 0 m :=
    ⟨sub_nonneg.2 hs.1.le,sub_le_sub_right hs.2 _⟩
  have hImage : ∀ᵐ s ∂ν, φ s ∈ E := by
    filter_upwards [hSupport'] with s hs
    rcases hs with rfl | hs
    · simpa only [φ,if_true] using (show ε*p ∈ E from hp)
    · have hs₀ : s ≠ 0 := (ha₀.trans hs.1).ne'
      have hG := (hgl (s-a) (hsRange s hs)).2.2 (sub_pos.2 hs.1)
      have h := hpK _ hG
      simpa only [φ,if_neg hs₀] using (show ε*(p - g (s-a)) ∈ E from h)
  have hAbs (v t : ℝ) : |ε*v-t|=|v-ε*t| := by
    rcases heps with h | h
    · simp only [h,one_mul]
    · rw [h]
      have he : (-1 : ℝ)*v-t=-(v-(-1 : ℝ)*t) := by ring
      rw [he,abs_neg]
  have hwitness (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : ∃ τ : ℝ,
      ν {τ}=0 ∧ Integrable (logDistance τ) ν ∧
      0 < ∫ x, logDistance τ x ∂ν ∧ (∀ᵐ s ∂ν, |s-τ| ≤ |φ s-t|) := by
    have htε : ε*t ∈ Icc (-1 : ℝ) 1 := by
      rcases heps with h | h
      · simpa only [h,one_mul] using ht
      · rw [h,neg_one_mul]
        exact ⟨by linarith only [ht.2],by linarith only [ht.1]⟩
    let u := p-ε*t
    have hu : u∈Icc a (a+2) := by
      change p-1 ≤ p-ε*t ∧ p-ε*t ≤ p-1+2
      constructor <;> linarith only [htε.1,htε.2]
    let τ := a+cumulative K u
    have hτ₀ : a ≤ τ := le_add_of_nonneg_right ENNReal.toReal_nonneg
    have hτu : τ ≤ u := by
      have h := cumulative_difference hK hu.1
      rw [cumulative_left hKsub,sub_zero] at h
      dsimp only [τ]
      linarith only [h]
    have hτm : τ∈Icc a (a+2) := ⟨hτ₀,hτu.trans hu.2⟩
    obtain ⟨hντ,hint,hpos⟩ := hνpot τ hτm
    refine ⟨τ,hντ,hint,hpos,?_⟩
    filter_upwards [hSupport'] with s hs
    rcases hs with rfl | hs
    · have hφ0 : φ 0 = ε*p := by simp [φ]
      rw [hφ0,hAbs,zero_sub,abs_neg,abs_of_nonneg (ha₀.le.trans hτ₀)]
      change τ ≤ |u|
      rw [abs_of_nonneg (ha₀.le.trans hu.1)]
      exact hτu
    · have hs₀ : s ≠ 0 := (ha₀.trans hs.1).ne'
      have h := (hgl (s-a) (hsRange s hs)).2.1
      have hd := (cumulative_lipschitz hK).dist_le_mul u (g (s-a))
      simp only [Real.dist_eq,NNReal.coe_one,one_mul,h] at hd
      have hl : cumulative K u-(s-a) = -(s-τ) := by dsimp only [τ]; ring
      rw [hl,abs_neg] at hd
      have hφs : φ s = ε*(p - g (s-a)) := by simp [φ,hs₀]
      rw [hφs,hAbs]
      have hr : p - g (s-a) - ε*t = u - g (s-a) := by dsimp only [u]; ring
      rwa [hr]
  exact normalize E hE.measurableSet hbox ν hν φ hφ hImage hwitness

end OMA.TaoTailTransport

theorem OMA.solution : OMA.R_Erdos1038_erdos_1038_parts_ii_R1_H2_R1.H1 :=
  OMA.TaoTailTransport.transfer
