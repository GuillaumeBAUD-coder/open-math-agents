import OMAReductions.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1
import Mathlib

/-! L² contraction under dilation for the Nyman–Beurling functions. -/

open MeasureTheory Filter
open scoped BigOperators

namespace RayDilation

noncomputable abbrev μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

noncomputable def raw (n : ℕ) (c θ : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * Int.fract (θ i / x)

lemma raw_ae (n : ℕ) (c θ : Fin n → ℝ) :
    ⇑(RiemannHypothesis.fractScalarInvSumL2 n c θ) =ᵐ[μ] raw n c θ := by
  let f (i : Fin n) : Lp ℝ 2 μ := (RiemannHypothesis.fractScalarInv_memLp2 (θ i)).toLp _
  have each (i : Fin n) : ∀ᵐ x ∂μ, (c i • f i) x = c i * Int.fract (θ i / x) := by
    filter_upwards [Lp.coeFn_smul (c i) (f i),
      (RiemannHypothesis.fractScalarInv_memLp2 (θ i)).coeFn_toLp] with x hs hf
    rw [hs]
    change c i * (f i) x = _
    rw [show (f i) x = Int.fract (θ i / x) from hf]
  apply (Lp.coeFn_fun_finsetSum Finset.univ (fun i => c i • f i)).trans
  filter_upwards [Filter.eventually_all.mpr each] with x hx
  exact Finset.sum_congr rfl fun i _ => hx i

lemma raw_scale (n : ℕ) (c θ : Fin n → ℝ) {a x : ℝ} (ha : 0 < a) (_ha1 : a ≤ 1)
    (hθ : ∀ i, θ i ∈ Set.Ioc 0 1) (hsum : ∑ i, c i * θ i = 0) (hx : 0 < x) :
    raw n c (fun i => a * θ i) x =
      (Set.Iic a).indicator (fun y => raw n c θ (y/a)) x := by
  by_cases hxa : x ≤ a
  · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hxa)]
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    field_simp
  · rw [Set.indicator_of_notMem (show x ∉ Set.Iic a from hxa)]
    unfold raw
    calc
      _ = ∑ i, (c i * θ i) * (a / x) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Int.fract_eq_self.mpr ⟨by positivity [((hθ i).1)],
          (div_lt_one hx).mpr ((mul_le_of_le_one_right ha.le (hθ i).2).trans_lt (lt_of_not_ge hxa))⟩]
        ring
      _ = 0 := by rw [← Finset.sum_mul, hsum, zero_mul]

end RayDilation

namespace RayDilation
open MeasureTheory Set
open scoped ENNReal

lemma compress_norm (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (g : ℝ → ℝ) :
    eLpNorm ((Iic a).indicator (fun x => g (x/a))) 2 (volume.restrict (Ioc 0 1)) ≤
      eLpNorm g 2 (volume.restrict (Ioc 0 1)) := by
  let D : ℝ → ℝ := fun x => x/a
  have emb : MeasurableEmbedding D := by
    simpa [D, div_eq_mul_inv] using
      (Homeomorph.mulRight₀ a⁻¹ (inv_ne_zero ha.ne')).toMeasurableEquiv.measurableEmbedding
  have pre : D ⁻¹' Ioc (0:ℝ) 1 = Ioc 0 a := by
    ext x
    change (0 < x/a ∧ x/a ≤ 1) ↔ (0 < x ∧ x ≤ a)
    simp [ha, div_pos_iff_of_pos_right, div_le_iff₀]
  have scaled : Measure.map D (volume.restrict (Ioc 0 a)) =
      ENNReal.ofReal a • volume.restrict (Ioc (0:ℝ) 1) := by
    rw [← pre, ← Measure.restrict_map emb.measurable measurableSet_Ioc]
    have m : Measure.map D volume = ENNReal.ofReal a • volume := by
      simpa [D, div_eq_mul_inv, abs_of_pos ha] using
        Real.map_volume_mul_right (inv_ne_zero ha.ne')
    simp [m]
  have inter : Iic a ∩ Ioc (0 : ℝ) 1 = Ioc 0 a := by
    ext x
    simp only [mem_inter_iff,mem_Iic,mem_Ioc]
    grind
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, inter]
  change eLpNorm (g ∘ D) 2 _ ≤ _
  rw [← emb.eLpNorm_map_measure, scaled]
  apply eLpNorm_mono_measure
  calc ENNReal.ofReal a • volume.restrict (Ioc (0:ℝ) 1)
      ≤ (1:ℝ≥0∞) • volume.restrict (Ioc (0:ℝ) 1) :=
        by
          intro s
          simp only [Measure.smul_apply, smul_eq_mul]
          exact mul_le_mul_left (by simpa using ENNReal.ofReal_le_ofReal ha1) _
    _ = _ := one_smul _ _

end RayDilation

namespace RayDilation

open MeasureTheory Set RiemannHypothesis

noncomputable def ray (a : ℝ) : Lp ℝ 2 μ :=
  indicatorConstLp 2 measurableSet_Iic (measure_ne_top μ (Iic a)) (1 : ℝ)

noncomputable def oneLp : Lp ℝ 2 μ :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℝ)

lemma scaled_edist {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (n : ℕ) (c θ : Fin n → ℝ)
    (hθ : ∀ i, θ i ∈ Ioc 0 1) (hsum : ∑ i, c i * θ i = 0) :
    edist (ray a) (fractScalarInvSumL2 n c (fun i => a * θ i)) ≤
      edist oneLp (fractScalarInvSumL2 n c θ) := by
  let g := fun x => 1 - raw n c θ x
  have hOne : ⇑oneLp =ᵐ[μ] fun _ => (1:ℝ) := by
    simpa [oneLp] using (indicatorConstLp_coeFn (p := 2) (μ := μ) (s := Set.univ)
      (hs := MeasurableSet.univ) (hμs := measure_ne_top μ _) (c := (1:ℝ)))
  have hRay : ⇑(ray a) =ᵐ[μ] (Iic a).indicator (fun _ => (1:ℝ)) :=
    indicatorConstLp_coeFn
  have hBase : ⇑oneLp - ⇑(fractScalarInvSumL2 n c θ) =ᵐ[μ] g := by
    filter_upwards [hOne,raw_ae n c θ] with x hx hy
    change oneLp x - fractScalarInvSumL2 n c θ x = 1 - raw n c θ x
    rw [hx,hy]
  have hxpos : ∀ᵐ x ∂μ, x ∈ Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  have hCut : ⇑(ray a) - ⇑(fractScalarInvSumL2 n c (fun i => a * θ i)) =ᵐ[μ]
      (Iic a).indicator (fun x => g (x/a)) := by
    filter_upwards [hRay,raw_ae n c (fun i => a * θ i),hxpos] with x hx hy hpos
    simp only [Pi.sub_apply,hx,hy, raw_scale n c θ ha ha1 hθ hsum hpos.1]
    by_cases h : x ∈ Iic a <;> simp [h,g]
  rw [Lp.edist_def, Lp.edist_def, eLpNorm_congr_ae hCut, eLpNorm_congr_ae hBase]
  exact compress_norm a ha ha1 g

lemma interior_ray {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    let S := { fractScalarInvSumL2 n c θ | (n) (c) (θ)
      (_ : ∀ i, θ i ∈ Ioc 0 1) (_ : ∑ i, c i * θ i = 0) }
    oneLp ∈ closure S → ray a ∈ closure S := by
  intro S h
  apply EMetric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨_, ⟨n, c, θ, hθ, hs, rfl⟩, hclose⟩ := EMetric.mem_closure_iff.mp h ε hε
  refine ⟨fractScalarInvSumL2 n c (fun i => a * θ i), ⟨n,c,_,?_,?_,rfl⟩, ?_⟩
  · exact fun i => ⟨mul_pos ha (hθ i).1, (mul_le_of_le_one_right ha.le (hθ i).2).trans ha1⟩
  · calc
      ∑ i, c i * (a * θ i) = a * ∑ i, c i * θ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = 0 := by rw [hs,mul_zero]
  · exact (scaled_edist ha ha1 n c θ hθ hs).trans_lt hclose

end RayDilation

namespace RayEdges
open MeasureTheory Set Filter RiemannHypothesis

noncomputable abbrev μ := volume.restrict (Ioc (0 : ℝ) 1)
noncomputable abbrev sums : Set (Lp ℝ 2 μ) :=
  {fractScalarInvSumL2 n c θ | (n) (c) (θ)
      (_hθ : ∀ i, θ i ∈ Ioc 0 1) (_h : ∑ i, c i * θ i = 0)}

lemma zero_mem_sums : (0 : Lp ℝ 2 μ) ∈ sums := by
  refine ⟨0, fun _ => 0, fun _ => 1, fun i => Fin.elim0 i, by simp, ?_⟩
  simp [fractScalarInvSumL2]

lemma ray_of_nonpos {a : ℝ} (ha : a ≤ 0) :
    indicatorConstLp 2 measurableSet_Iic (measure_ne_top μ (Iic a)) (1:ℝ) ∈ closure sums := by
  have he : indicatorConstLp 2 measurableSet_Iic (measure_ne_top μ (Iic a)) (1:ℝ) = 0 := by
    apply Lp.ext
    have hs : ∀ᵐ x ∂μ, x ∈ Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
    filter_upwards [@indicatorConstLp_coeFn _ _ _ 2 _ _ _ measurableSet_Iic
      (measure_ne_top μ (Iic a)) (1:ℝ), hs, Lp.coeFn_zero ℝ 2 μ] with x hx hmem hz
    rw [hx, hz, indicator_of_notMem (show x ∉ Iic a from not_le_of_gt (ha.trans_lt hmem.1))]
    rfl
  rw [he]
  exact subset_closure zero_mem_sums

lemma ray_of_one_le {a : ℝ} (ha : 1 ≤ a)
    (one : indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1:ℝ) ∈ closure sums) :
    indicatorConstLp 2 measurableSet_Iic (measure_ne_top μ (Iic a)) (1:ℝ) ∈ closure sums := by
  have he : indicatorConstLp 2 measurableSet_Iic (measure_ne_top μ (Iic a)) (1:ℝ) =
      indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1:ℝ) := by
    apply Lp.ext
    have hs : ∀ᵐ x ∂μ, x ∈ Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
    filter_upwards [@indicatorConstLp_coeFn _ _ _ 2 _ _ _ measurableSet_Iic
      (measure_ne_top μ (Iic a)) (1:ℝ), hs, @indicatorConstLp_coeFn _ _ _ 2 _ _ _
      MeasurableSet.univ (measure_ne_top μ univ) (1:ℝ)] with x hx hm hu
    rw [hx, hu, indicator_of_mem (show x ∈ Iic a from hm.2.trans ha), indicator_of_mem (mem_univ x)]
  simpa only [he] using one
end RayEdges

theorem OMA.solution : OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1.H2 := by
  change RayDilation.oneLp ∈ closure RayEdges.sums → ∀ a : ℝ, RayDilation.ray a ∈ closure RayEdges.sums
  intro one a
  rcases le_or_gt a 0 with ha | ha
  · exact RayEdges.ray_of_nonpos ha
  rcases le_or_gt 1 a with h1 | h1
  · exact RayEdges.ray_of_one_le h1 one
  · exact RayDilation.interior_ray ha h1.le one
