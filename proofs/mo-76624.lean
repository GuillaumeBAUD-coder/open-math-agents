import OMAStatements.S_mo_76624
import Mathlib

/-!
MathOverflow 76624: the counterexample of Anthony Quas's comment and Jeff Schenker's answer, in a
simple form. On `Ω = [0, 1]` with the uniform law, let `X_n(t)(ω) = 1` if `|ω - t| < 1/(n+1)` and
`0` otherwise. Then `E|X_n(t)| ≤ 2/(n+1)` for every `t`, while `sup_{t ∈ [0,1]} X_n(t)(ω) = 1`
for every `ω` (take `t = ω`), so `E sup_t |X_n(t)| ≥ 1`.
-/

namespace OMA.P76624

open MeasureTheory Filter Topology

/-- The window of half-width `1/(n+1)` around `t`. -/
def W (n : ℕ) (t : ℝ) : Set ℝ := Set.Ioo (t - 1 / ((n : ℝ) + 1)) (t + 1 / ((n : ℝ) + 1))

/-- `X n t ω = 1` if `|ω - t| < 1/(n+1)`, else `0`. -/
noncomputable def X (n : ℕ) (t : ℝ) : ℝ → ℝ := (W n t).indicator 1

/-- The uniform law on `[0, 1]`. -/
noncomputable def μ : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩

lemma ofReal_X (n : ℕ) (t ω : ℝ) :
    ENNReal.ofReal |X n t ω| = (W n t).indicator 1 ω := by
  by_cases h : ω ∈ W n t <;> simp [X, h]

lemma meas (n : ℕ) (t : ℝ) : Measurable (X n t) :=
  measurable_one.indicator measurableSet_Ioo

lemma bound (n : ℕ) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal |X n t ω| ∂μ ≤ ENNReal.ofReal (2 / ((n : ℝ) + 1)) := by
  simp_rw [ofReal_X]
  rw [lintegral_indicator_one (show MeasurableSet (W n t) from measurableSet_Ioo)]
  calc μ (W n t) ≤ volume (W n t) := by
        simp only [μ]; exact Measure.restrict_apply_le _ _
    _ = ENNReal.ofReal (2 / ((n : ℝ) + 1)) := by
        rw [W, Real.volume_Ioo]; congr 1; ring

lemma hyp : Tendsto (fun n => ⨆ t ∈ Set.Icc (0 : ℝ) 1, ∫⁻ ω, ENNReal.ofReal |X n t ω| ∂μ)
    atTop (𝓝 0) := by
  have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (2 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    have := (show Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) from
      tendsto_one_div_add_atTop_nhds_zero_nat).const_mul 2
    simpa [div_eq_mul_inv] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => bot_le) ?_
  intro n
  exact iSup₂_le fun t _ => bound n t

lemma big (n : ℕ) : 1 ≤ ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) 1, ENNReal.ofReal |X n t ω| ∂μ := by
  have hμ : ∫⁻ _ω, (1 : ENNReal) ∂μ = 1 := by simp
  rw [← hμ]
  apply lintegral_mono_ae
  have : ∀ᵐ ω ∂μ, ω ∈ Set.Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
  filter_upwards [this] with ω hω
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hmem : ω ∈ W n ω := ⟨by linarith, by linarith⟩
  calc (1 : ENNReal) = ENNReal.ofReal |X n ω ω| := by simp [X, hmem]
    _ ≤ ⨆ t ∈ Set.Icc (0 : ℝ) 1, ENNReal.ofReal |X n t ω| :=
        le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) 1) => ENNReal.ofReal |X n t ω|) ω hω

lemma disproof_aux : ¬ (∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (T : ℝ) (X : ℕ → ℝ → Ω → ℝ), 0 < T → (∀ n t, Measurable (X n t)) →
      Tendsto (fun n => ⨆ t ∈ Set.Icc 0 T, ∫⁻ ω, ENNReal.ofReal |X n t ω| ∂μ) atTop (𝓝 0) →
      Tendsto (fun n => ∫⁻ ω, ⨆ t ∈ Set.Icc 0 T, ENNReal.ofReal |X n t ω| ∂μ) atTop (𝓝 0)) := by
  intro h
  have hc := h ℝ μ 1 X one_pos meas hyp
  have : (1 : ENNReal) ≤ 0 := ge_of_tendsto hc (Eventually.of_forall big)
  simp at this

end OMA.P76624

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_76624.main) := OMA.P76624.disproof_aux
