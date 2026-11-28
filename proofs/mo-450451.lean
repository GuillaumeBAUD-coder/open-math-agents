import OMAStatements.S_mo_450451

/-!
# A counterexample to uniformity in paired Lebesgue differentiation

Problem: https://mathoverflow.net/questions/450451
Credit: @CubeJerry

Take Lebesgue measure restricted to [0,1]. For each sufficiently small u>0,
let f be the indicator of [0,u] divided by u and g its indicator. At radius 2u,
the centered average of g is at most 1/2 everywhere on the support of f,
whereas the integral of f*g is 1. This refutes the proposed uniform bound.
The source's separate fixed-function convergence question is not used.
-/

namespace MO450451Proof
open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable def μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance : IsFiniteMeasure μ := by
  refine ⟨?_⟩
  simp [μ, Measure.restrict_apply, Real.volume_Icc]

theorem mass_interval (u : ℝ) (_hu : 0 ≤ u) (hu1 : u ≤ 1) :
    μ (Icc 0 u) = ENNReal.ofReal u := by
  have hs : Icc (0 : ℝ) u ⊆ Icc 0 1 := fun x hx => ⟨hx.1, hx.2.trans hu1⟩
  rw [μ, Measure.restrict_apply measurableSet_Icc, inter_eq_left.mpr hs]
  simp [Real.volume_Icc]

noncomputable def F (u : ℝ) : ℝ → ℝ≥0 :=
  (Icc (0 : ℝ) u).indicator fun _ => Real.toNNReal u⁻¹
noncomputable def G (u : ℝ) : ℝ → ℝ≥0 :=
  (Icc (0 : ℝ) u).indicator fun _ => 1

theorem measurable_F (u : ℝ) : Measurable (F u) :=
  measurable_const.indicator measurableSet_Icc

theorem measurable_G (u : ℝ) : Measurable (G u) :=
  measurable_const.indicator measurableSet_Icc

theorem G_le_one (u x : ℝ) : G u x ≤ 1 := by
  classical
  by_cases hx : x ∈ Icc (0 : ℝ) u <;> simp [G, hx]

theorem coe_F (u x : ℝ) : (F u x : ℝ≥0∞) =
    (Icc (0 : ℝ) u).indicator (fun _ => ENNReal.ofReal u⁻¹) x := by
  classical
  by_cases hx : x ∈ Icc (0 : ℝ) u <;> simp [F, hx, ENNReal.ofReal]

theorem coe_G (u x : ℝ) : (G u x : ℝ≥0∞) =
    (Icc (0 : ℝ) u).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  classical
  by_cases hx : x ∈ Icc (0 : ℝ) u <;> simp [G, hx]

theorem lintegral_F (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) :
    (∫⁻ x, (F u x : ℝ≥0∞) ∂μ) = 1 := by
  simp_rw [coe_F]
  rw [lintegral_indicator_const measurableSet_Icc,
    mass_interval u hu.le hu1, ENNReal.ofReal_inv_of_pos hu]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hu) ENNReal.ofReal_ne_top

theorem lintegral_G (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (∫⁻ x, (G u x : ℝ≥0∞) ∂μ) = ENNReal.ofReal u := by
  simp_rw [coe_G]
  rw [lintegral_indicator_const measurableSet_Icc, one_mul, mass_interval u hu hu1]

theorem lintegral_FG (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) :
    (∫⁻ x, (F u x : ℝ≥0∞) * (G u x : ℝ≥0∞) ∂μ) = 1 := by
  rw [← lintegral_F u hu hu1]
  apply lintegral_congr
  intro x
  classical
  by_cases hx : x ∈ Icc (0 : ℝ) u <;> simp [F, G, hx]

end MO450451Proof

namespace MO450451Proof
open MeasureTheory Set OMA.S_mo_450451
open scoped ENNReal NNReal

theorem average_le (u x : ℝ) (hu : 0 < u) (hu2 : 2 * u ≤ 1)
    (hx : x ∈ Icc (0 : ℝ) u) :
    centeredAverage μ (2 * u) (G u) x ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
  have hu1 : u ≤ 1 := by linarith
  have hn : (∫⁻ y in Icc (x - 2 * u) (x + 2 * u), (G u y : ℝ≥0∞) ∂μ) ≤
      ENNReal.ofReal u := by
    calc
      _ ≤ ∫⁻ y, (G u y : ℝ≥0∞) ∂μ := setLIntegral_le_lintegral _ _
      _ = _ := lintegral_G u hu.le hu1
  have hd : ENNReal.ofReal (2 * u) ≤ μ (Icc (x - 2 * u) (x + 2 * u)) := by
    rw [← mass_interval (2 * u) (by positivity) hu2]
    apply measure_mono
    intro y hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hdiv := ENNReal.div_le_div hn hd
  change centeredAverage μ (2 * u) (G u) x ≤
    ENNReal.ofReal u / ENNReal.ofReal (2 * u) at hdiv
  have heq : u / (2 * u) = (1 / 2 : ℝ) := by
    apply (div_eq_iff (by positivity : (2 * u) ≠ 0)).mpr
    ring
  rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < 2 * u), heq] at hdiv
  exact hdiv

theorem paired_bound (u : ℝ) (hu : 0 < u) (hu2 : 2 * u ≤ 1) :
    (∫⁻ x, (F u x : ℝ≥0∞) * centeredAverage μ (2 * u) (G u) x ∂μ) ≤
      ENNReal.ofReal (1 / 2 : ℝ) := by
  have hu1 : u ≤ 1 := by linarith
  calc
    _ ≤ ∫⁻ x, (F u x : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ) ∂μ := by
      apply lintegral_mono
      intro x
      classical
      by_cases hx : x ∈ Icc (0 : ℝ) u
      · exact mul_le_mul_of_nonneg_left (average_le u x hu hu2 hx) zero_le
      · simp [F, hx]
    _ = (∫⁻ x, (F u x : ℝ≥0∞) ∂μ) * ENNReal.ofReal (1 / 2 : ℝ) :=
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ = _ := by rw [lintegral_F u hu hu1, one_mul]

theorem paired_error (u : ℝ) (hu : 0 < u) (hu2 : 2 * u ≤ 1) :
    (1 / 2 : ℝ) ≤
      |(∫⁻ x, (F u x : ℝ≥0∞) * centeredAverage μ (2 * u) (G u) x ∂μ).toReal -
        (∫⁻ x, (F u x : ℝ≥0∞) * (G u x : ℝ≥0∞) ∂μ).toReal| := by
  have hu1 : u ≤ 1 := by linarith
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (paired_bound u hu hu2)
  norm_num only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
  rw [lintegral_FG u hu hu1]
  norm_num only [ENNReal.toReal_one]
  rw [abs_of_nonpos (by linarith)]
  linarith

end MO450451Proof

namespace MO450451Proof
open MeasureTheory Set OMA.S_mo_450451
open scoped ENNReal NNReal

theorem not_uniform : ¬ (∀ (μ : Measure ℝ), IsFiniteMeasure μ → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
        ∀ f g : ℝ → ℝ≥0, Measurable f → Measurable g →
          (∫⁻ x, (f x : ℝ≥0∞) ∂μ) ≤ 1 → (∀ x, g x ≤ 1) →
            |(∫⁻ x, (f x : ℝ≥0∞) * centeredAverage μ r g x ∂μ).toReal -
                (∫⁻ x, (f x : ℝ≥0∞) * (g x : ℝ≥0∞) ∂μ).toReal| < ε) := by
  intro H
  obtain ⟨δ, hδ, h⟩ := H μ inferInstance (1 / 4) (by norm_num)
  let u : ℝ := min (δ / 4) (1 / 4)
  have hu : 0 < u := lt_min (by linarith) (by norm_num)
  have huδ : u ≤ δ / 4 := min_le_left _ _
  have hu4 : u ≤ 1 / 4 := min_le_right _ _
  have hu2 : 2 * u ≤ 1 := by linarith
  have hu1 : u ≤ 1 := by linarith
  have hr : 2 * u < δ := by linarith
  have hh := h (2 * u) (by positivity) hr (F u) (G u)
    (measurable_F u) (measurable_G u) (lintegral_F u hu hu1).le (G_le_one u)
  have he := paired_error u hu hu2
  linarith

end MO450451Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_450451.main) := by
  exact MO450451Proof.not_uniform
