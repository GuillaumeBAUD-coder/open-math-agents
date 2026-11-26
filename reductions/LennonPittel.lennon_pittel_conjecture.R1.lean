import FormalConjectures.Paper.LennonPittelStableMatchings
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.NormNum

open MeasureTheory Filter
open scoped Topology ENNReal
-- Conditional reduction by @harshshah1618.
-- H2 is unproved and stronger than the original conjecture.
-- The implication is Markov's inequality applied to the reciprocal count.
namespace OMA.R_LennonPittel_lennon_pittel_conjecture_R1

lemma lower_tail_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (M ε : ℝ) (hε : 0 < ε) (hf : ∀ x, 0 < f x)
    (hm : AEMeasurable (fun x => ENNReal.ofReal (M / f x)) μ) :
    μ {x | f x < ε * M} ≤ ENNReal.ofReal ε * ∫⁻ x, ENNReal.ofReal (M / f x) ∂μ := by
  have he0 : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  calc
    μ {x | f x < ε * M} ≤ μ {x | (ENNReal.ofReal ε)⁻¹ ≤ ENNReal.ofReal (M / f x)} := by
      apply measure_mono
      intro x hx
      change f x < ε * M at hx
      rw [← ENNReal.ofReal_inv_of_pos hε]
      apply ENNReal.ofReal_le_ofReal
      apply (le_div_iff₀ (hf x)).mpr
      have hh : f x / ε < M := (div_lt_iff₀ hε).mpr (by simpa only [mul_comm] using hx)
      simpa only [div_eq_mul_inv, mul_comm] using hh.le
    _ ≤ (∫⁻ x, ENNReal.ofReal (M / f x) ∂μ) / (ENNReal.ofReal ε)⁻¹ :=
      meas_ge_le_lintegral_div hm (by simp) (by simpa using he0)
    _ = ENNReal.ofReal ε * ∫⁻ x, ENNReal.ofReal (M / f x) ∂μ := by
      rw [div_eq_mul_inv, inv_inv, mul_comm]

/-- Every complete strict preference profile has a stable complete matching. -/
def H1 : Prop := ∀ n (p : StableMarriage.Profile n), 0 < StableMarriage.numStableMatchings p

/-- A uniform normalized reciprocal-moment bound: the unresolved quantitative step. -/
def H2 : Prop := ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
  (∫⁻ p : StableMarriage.Profile n,
    ENNReal.ofReal (StableMarriage.expectedNumStableMatchings n /
      (StableMarriage.numStableMatchings p : ℝ)) ∂(StableMarriage.uniformProfile n).toMeasure) ≤ C

theorem main : H1 → H2 → type_of% @LennonPittel.lennon_pittel_conjecture := by
  intro hpos ⟨C, hC, hbound⟩ ε hεpos _hεanti hεlim
  let μ (n : ℕ) := (StableMarriage.uniformProfile n).toMeasure
  have hε0 : Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hεlim
  have hlim : Tendsto (fun n => ENNReal.ofReal (ε n) * C) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hε0 (Or.inr hC)
  have hbad : Tendsto (fun n => μ n
      {p | (StableMarriage.numStableMatchings p : ℝ) < ε n * StableMarriage.expectedNumStableMatchings n})
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
    intro n
    exact (lower_tail_bound (μ n) (fun p => (StableMarriage.numStableMatchings p : ℝ))
      (StableMarriage.expectedNumStableMatchings n) (ε n) (hεpos n)
      (fun p => Nat.cast_pos.mpr (hpos n p))
      (measurable_of_countable _).aemeasurable).trans (mul_le_mul' (le_refl _) (hbound n))
  have hgood (n : ℕ) : μ n
      {p | (StableMarriage.numStableMatchings p : ℝ) ≥ ε n * StableMarriage.expectedNumStableMatchings n} =
      1 - μ n {p | (StableMarriage.numStableMatchings p : ℝ) < ε n * StableMarriage.expectedNumStableMatchings n} := by
    have heq : {p : StableMarriage.Profile n | (StableMarriage.numStableMatchings p : ℝ) ≥
        ε n * StableMarriage.expectedNumStableMatchings n} =
        {p | (StableMarriage.numStableMatchings p : ℝ) < ε n * StableMarriage.expectedNumStableMatchings n}ᶜ := by
      ext p; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
    rw [heq, measure_compl MeasurableSpace.measurableSet_top (measure_ne_top _ _), measure_univ]
  change Tendsto (fun n => μ n _) atTop (𝓝 1)
  simp_rw [hgood]
  simpa only [Function.comp_def, tsub_zero] using ((ENNReal.continuous_sub_left (a := 1) (by simp)).tendsto 0).comp hbad

end OMA.R_LennonPittel_lennon_pittel_conjecture_R1
