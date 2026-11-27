import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1_H2_R1

/-! Jointly measurable representative of a continuous L² field.
Port of OpenAI, openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a,
as adapted by Jacob Parish in plasma-ai/erdos-173 at 4a368a652753.
Both sources are used under Apache-2.0. -/
-- Credit: @marcusbuffett

noncomputable section
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal
namespace PlaneRepresentative
variable {T X : Type*} [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
  [MeasurableSpace T] [BorelSpace T] [MeasurableSpace X] (μ : Measure X)
  (f : T → Lp ℂ 2 μ) (hf : Continuous f)
include hf
omit [MeasurableSpace T] [BorelSpace T] in
lemma dense_approx (t : T) (ε : ℝ) (hε : 0 < ε) :
    ∃ n, dist (f (TopologicalSpace.denseSeq T n)) (f t) < ε := by
  have h := mem_closure_image hf.continuousAt (TopologicalSpace.denseRange_denseSeq T t)
  rw [← Set.range_comp] at h
  obtain ⟨n,hn⟩ := Metric.mem_closure_range_iff.mp h ε hε
  exact ⟨n,by simpa only [Function.comp_apply,dist_comm] using hn⟩
def approxIndex (n : ℕ) (t : T) : ℕ := Nat.find (dense_approx μ f hf t ((1/2:ℝ)^n) (by positivity))
lemma index_measurable (n : ℕ) : Measurable (approxIndex μ f hf n) := by
  apply measurable_find
  intro j
  exact isOpen_lt (continuous_const.dist hf) continuous_const |>.measurableSet
omit [MeasurableSpace T] [BorelSpace T] in
lemma index_bound (n : ℕ) (t : T) :
    dist (f (TopologicalSpace.denseSeq T (approxIndex μ f hf n t))) (f t) < (1/2:ℝ)^n := by
  unfold approxIndex
  exact Nat.find_spec (dense_approx μ f hf t ((1/2:ℝ)^n) (by positivity))
def approxField (n : ℕ) (p : T × X) : ℂ :=
  f (TopologicalSpace.denseSeq T (approxIndex μ f hf n p.1)) p.2
lemma approxField_measurable (n : ℕ) : Measurable (approxField μ f hf n) := by
  have h : Measurable (fun p : ℕ × X => f (TopologicalSpace.denseSeq T p.1) p.2) :=
    measurable_from_prod_countable_right fun j => (Lp.stronglyMeasurable (f (TopologicalSpace.denseSeq T j))).measurable
  exact h.comp (((index_measurable μ f hf n).comp measurable_fst).prodMk measurable_snd)
omit [MeasurableSpace T] [BorelSpace T] in
lemma approxField_tendsto (t : T) : ∀ᵐ x ∂μ,
    Tendsto (fun n => approxField μ f hf n (t,x)) atTop (𝓝 (f t x)) := by
  let g : ℕ → Lp ℂ 2 μ := fun n => f (TopologicalSpace.denseSeq T (approxIndex μ f hf n t))-f t
  have hs : Summable (fun n => ‖g n‖) := summable_geometric_two.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by simpa only [g,dist_eq_norm] using (index_bound μ f hf n t).le)
  have ha : ∀ᵐ x ∂μ, Summable (fun n => ‖g n x‖) := by
    apply summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1:ℝ≥0∞) ≤ 2) (fun n => Lp.aestronglyMeasurable (g n))
    simpa only [← Lp.enorm_def] using (tsum_enorm_ne_top_iff_summable_norm.mpr hs)
  have he : ∀ᵐ x ∂μ, ∀ n, g n x = approxField μ f hf n (t,x)-f t x :=
    ae_all_iff.mpr fun n => Lp.coeFn_sub _ _
  filter_upwards [ha,he] with x hx he
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [he] using hx.tendsto_atTop_zero
def measurableField (p : T × X) : ℂ :=
  ⟨limsup (fun n => (approxField μ f hf n p).re) atTop,
   limsup (fun n => (approxField μ f hf n p).im) atTop⟩
lemma measurableField_measurable : Measurable (measurableField μ f hf) := by
  have hr := Measurable.limsup fun n => Complex.continuous_re.measurable.comp (approxField_measurable μ f hf n)
  have hi := Measurable.limsup fun n => Complex.continuous_im.measurable.comp (approxField_measurable μ f hf n)
  have hh := (Complex.continuous_ofReal.measurable.comp hr).add ((Complex.continuous_ofReal.measurable.comp hi).mul_const Complex.I)
  convert hh using 1
  funext p
  apply Complex.ext <;> simp [measurableField]
lemma exists_measurable_field : ∃ F : T × X → ℂ, Measurable F ∧ ∀ t, (fun x => F (t,x)) =ᵐ[μ] f t := by
  refine ⟨measurableField μ f hf,?_,?_⟩
  · exact measurableField_measurable μ f hf
  · intro t
    filter_upwards [approxField_tendsto μ f hf t] with x hx
    apply Complex.ext
    · exact (Complex.continuous_re.continuousAt.tendsto.comp hx).limsup_eq
    · exact (Complex.continuous_im.continuousAt.tendsto.comp hx).limsup_eq
end PlaneRepresentative
end

theorem OMA.solution : OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1.H2 :=
  fun _ _ ν f hf => PlaneRepresentative.exists_measurable_field ν f hf
