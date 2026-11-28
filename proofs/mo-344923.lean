import OMAStatements.S_mo_344923
import Mathlib

open MeasureTheory
open scoped ENNReal

open OMA.S_mo_344923 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_344923.main) := by
  intro h
  let z₀ : ℝ × ℝ := (0, 0)
  let z₁ : ℝ × ℝ := (1, 1)
  let c : ℝ≥0∞ := ENNReal.ofReal (1 / 2)
  let μ : Measure (ℝ × ℝ) := c • (Measure.dirac z₀ + Measure.dirac z₁)
  have hc : c ≠ 0 := by norm_num [c]
  have hμ {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
      μ s = c * (s.indicator 1 z₀ + s.indicator 1 z₁) := by
    simp [μ, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hs, mul_add]
  have hprob : IsProbabilityMeasure μ := by
    constructor
    rw [hμ MeasurableSet.univ]
    simp only [Set.indicator_univ, Pi.one_apply]
    have he : (1 : ℝ≥0∞) + 1 = ENNReal.ofReal 2 := by norm_num
    rw [he, show c = ENNReal.ofReal (1 / 2) from rfl,
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  let _ : IsProbabilityMeasure μ := hprob
  let s : Set ℝ := {0}
  let t : Set ℝ := {1}
  have hs : MeasurableSet s := measurableSet_singleton _
  have ht : MeasurableSet t := measurableSet_singleton _
  have hfst : μ.fst s = c := by
    rw [Measure.fst_apply hs, hμ (measurable_fst hs)]
    norm_num [s, z₀, z₁, Set.indicator_apply]
  have hsnd : μ.snd t = c := by
    rw [Measure.snd_apply ht, hμ (measurable_snd ht)]
    norm_num [t, z₀, z₁, Set.indicator_apply]
  have hrect : μ (s ×ˢ t) = 0 := by
    rw [hμ (hs.prod ht)]
    norm_num [s, t, z₀, z₁, Set.indicator_apply]
  have hne : μ ≠ μ.fst.prod μ.snd := by
    intro he
    have hval := congrArg (fun ν : Measure (ℝ × ℝ) => ν (s ×ˢ t)) he
    rw [hrect, Measure.prod_prod, hfst, hsnd] at hval
    exact (mul_ne_zero hc hc) hval.symm
  have kl := h ℝ ℝ μ hprob (fun _ => 0) (LipschitzWith.const' 0)
  change mutualInformation (μ.map (fun _ => z₀)) = mutualInformation μ at kl
  rw [Measure.map_const, hprob.measure_univ, one_smul] at kl
  have hf : (Measure.dirac z₀).fst = Measure.dirac (0 : ℝ) :=
    Measure.map_dirac' measurable_fst _
  have hg : (Measure.dirac z₀).snd = Measure.dirac (0 : ℝ) :=
    Measure.map_dirac' measurable_snd _
  unfold mutualInformation at kl
  rw [hf, hg, Measure.dirac_prod_dirac, InformationTheory.klDiv_self] at kl
  exact hne (InformationTheory.klDiv_eq_zero_iff.mp kl.symm)