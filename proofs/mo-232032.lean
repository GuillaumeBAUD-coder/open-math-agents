import OMAStatements.S_mo_232032
import Mathlib

namespace TwoPointDivergence

open OMA.S_mo_232032 MeasureTheory InformationTheory Real
open scoped ENNReal NNReal

universe u

private abbrev Space := ULift.{u} Bool
private def lpt : Space.{u} := ⟨false⟩
private def rpt : Space.{u} := ⟨true⟩
local instance : MeasurableSpace Space.{u} := ⊤
local instance : MeasurableSingletonClass Space.{u} := ⟨fun _ => trivial⟩

private noncomputable def coin (a b : ℝ≥0) : Measure Space.{u} :=
  a • Measure.dirac lpt + b • Measure.dirac rpt

private theorem coin_univ (a b : ℝ≥0) (h : a + b = 1) : coin a b Set.univ = 1 := by
  simpa [coin, Measure.add_apply, Measure.coe_nnreal_smul_apply] using
    congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h

private noncomputable def prob (a b : ℝ≥0) (h : a + b = 1) : ProbabilityMeasure Space.{u} :=
  ⟨coin a b, ⟨coin_univ a b h⟩⟩

private theorem coin_lpt (a b : ℝ≥0) : coin a b {lpt} = (a : ℝ≥0∞) := by
  simp [coin, Measure.add_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _), lpt, rpt]

private theorem coin_rpt (a b : ℝ≥0) : coin a b {rpt} = (b : ℝ≥0∞) := by
  simp [coin, Measure.add_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _), lpt, rpt]

private theorem ac_coin (a b c d : ℝ≥0) (hc : c ≠ 0) (hd : d ≠ 0) :
    coin a b ≪ coin c d := by
  intro s hs
  simp only [coin, Measure.add_apply, Measure.coe_nnreal_smul_apply] at hs ⊢
  obtain ⟨h₁,h₂⟩ := add_eq_zero.mp hs
  have h₃ := (mul_eq_zero.mp h₁).resolve_left (ENNReal.coe_ne_zero.mpr hc)
  have h₄ := (mul_eq_zero.mp h₂).resolve_left (ENNReal.coe_ne_zero.mpr hd)
  simp [h₃,h₄]

private theorem integral_coin (a b : ℝ≥0) (f : Space.{u} → ℝ) :
    (∫ x, f x ∂coin a b) = (a : ℝ) * f lpt + (b : ℝ) * f rpt := by
  have h₁ : Integrable f (a • Measure.dirac lpt) :=
    (integrable_dirac (by simp)).smul_measure_nnreal
  have h₂ : Integrable f (b • Measure.dirac rpt) :=
    (integrable_dirac (by simp)).smul_measure_nnreal
  rw [coin, integral_add_measure h₁ h₂]
  simp [integral_smul_nnreal_measure, NNReal.smul_def]

private theorem int_coin (a b : ℝ≥0) (f : Space.{u} → ℝ) : Integrable f (coin a b) := by
  rw [coin, integrable_add_measure]
  exact ⟨(integrable_dirac (by simp)).smul_measure_nnreal,
    (integrable_dirac (by simp)).smul_measure_nnreal⟩

private theorem rn_at_point (μ ν : Measure Space.{u}) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ ≪ ν) (x : Space.{u}) (h₀ : ν {x} ≠ 0) (h₁ : ν {x} ≠ ∞) :
    μ.rnDeriv ν x = μ {x} / ν {x} := by
  have he : (ν.withDensity (μ.rnDeriv ν)) {x} = μ {x} :=
    congrArg (fun M : Measure Space.{u} => M {x}) (Measure.withDensity_rnDeriv_eq μ ν h)
  rw [withDensity_apply _ (measurableSet_singleton x), lintegral_singleton] at he
  exact (ENNReal.eq_div_iff h₀ h₁).mpr (by simpa [mul_comm] using he)

private theorem coin_kl (a b c d : ℝ≥0) (hab : a+b=1) (hcd : c+d=1)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    klDiv (coin a b) (coin c d) =
      ENNReal.ofReal ((a : ℝ) * log ((a : ℝ) / c) + (b : ℝ) * log ((b : ℝ) / d)) := by
  let _ : IsProbabilityMeasure (coin a b) := ⟨coin_univ a b hab⟩
  let _ : IsProbabilityMeasure (coin c d) := ⟨coin_univ c d hcd⟩
  have h := ac_coin a b c d hc hd
  have hl := rn_at_point (coin a b) (coin c d) h lpt (by simpa only [coin_lpt] using ENNReal.coe_ne_zero.mpr hc)
    (by rw [coin_lpt]; exact ENNReal.coe_ne_top)
  have hr := rn_at_point (coin a b) (coin c d) h rpt (by simpa only [coin_rpt] using ENNReal.coe_ne_zero.mpr hd)
    (by rw [coin_rpt]; exact ENNReal.coe_ne_top)
  rw [klDiv_of_ac_of_integrable h (int_coin a b _), integral_coin]
  simp [llr_def, hl, hr, coin_lpt, coin_rpt, ENNReal.toReal_div, measureReal_def, coin_univ a b hab, coin_univ c d hcd]

private theorem mix_coin (a b c d : ℝ≥0) :
    mixture (coin a b) (coin c d) = coin ((a+c)/2) ((b+d)/2) := by
  simp only [mixture, coin]
  rw [add_add_add_comm, ← add_smul, ← add_smul, smul_add, smul_smul, smul_smul]
  rw [inv_mul_eq_div, inv_mul_eq_div]

private theorem js_less :
    jsDiv (coin (1/2) (1/2)) (coin 0 1) < jsDiv (coin 1 0) (coin 0 1) := by
  have hmix₀ : mixture (coin 1 0) (coin 0 1) = coin (1/2) (1/2) := by
    rw [mix_coin]
    norm_num
  have hmix₁ : mixture (coin (1/2) (1/2)) (coin 0 1) = coin (1/4) (3/4) := by
    rw [mix_coin]
    norm_num
  have h₀ : jsDiv (coin 1 0) (coin 0 1) =
      (ENNReal.ofReal (log 2) + ENNReal.ofReal (log 2)) / 2 := by
    unfold jsDiv
    rw [hmix₀, coin_kl 1 0 _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      coin_kl 0 1 _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have h₁ : jsDiv (coin (1/2) (1/2)) (coin 0 1) =
      (ENNReal.ofReal (1/2 * log 2 + 1/2 * log (2/3)) + ENNReal.ofReal (log (4/3))) / 2 := by
    unfold jsDiv
    rw [hmix₁, coin_kl (1/2) (1/2) _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      coin_kl 0 1 _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have hl : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hd : log ((2:ℝ)/3) < 0 := log_neg (by norm_num) (by norm_num)
  have he₁ : ENNReal.ofReal (1/2 * log 2 + 1/2 * log (2/3)) < ENNReal.ofReal (log 2) :=
    (ENNReal.ofReal_lt_ofReal_iff hl).mpr (by linarith)
  have he₂ : ENNReal.ofReal (log (4/3)) < ENNReal.ofReal (log 2) :=
    (ENNReal.ofReal_lt_ofReal_iff hl).mpr (log_lt_log (by norm_num) (by norm_num))
  rw [h₁, h₀]
  have hsum := ENNReal.add_lt_add_of_le_of_lt ENNReal.ofReal_ne_top he₁.le he₂
  simpa only [div_eq_mul_inv, mul_comm] using
    ENNReal.mul_lt_mul_right (a := (2 : ℝ≥0∞)⁻¹) (by norm_num) (by simp) hsum

private theorem singular_kl : klDiv (coin (1/2) (1/2)) (coin 0 1) = ∞ := by
  apply klDiv_of_not_ac
  intro h
  have e : coin (1/2) (1/2) {lpt} = 0 := h (by simp [coin_lpt])
  norm_num [coin_lpt] at e

end TwoPointDivergence

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_232032.main) := by
  intro h
  have hlt := h TwoPointDivergence.Space (TwoPointDivergence.prob 1 0 (by norm_num)) (TwoPointDivergence.prob 0 1 (by norm_num))
    (TwoPointDivergence.prob (1/2) (1/2) (by norm_num)) (TwoPointDivergence.prob 0 1 (by norm_num)) TwoPointDivergence.js_less
  change InformationTheory.klDiv (TwoPointDivergence.coin (1/2) (1/2)) (TwoPointDivergence.coin 0 1) < _ at hlt
  rw [TwoPointDivergence.singular_kl] at hlt
  exact (not_lt_of_ge le_top) hlt