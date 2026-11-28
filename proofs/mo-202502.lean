import OMAStatements.S_mo_202502
import Mathlib

-- Problem: mo-202502, does E e^{tX} <= E e^{tY} for all t > 0 imply P(X > x) <= P(Y > x) for
-- all x?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Let X = 1 and let Y be 0 or 2 with probability 1/2 each. Then
-- E e^{tY} = (1 + e^{2t})/2 >= e^t = E e^{tX} since (e^t - 1)^2 >= 0, but
-- P(X > 1/2) = 1 > 1/2 = P(Y > 1/2).

open MeasureTheory ProbabilityTheory Set

namespace MO202502

theorem int_dirac (a t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (Measure.dirac a) :=
  integrable_dirac (by simp)

noncomputable def ν : Measure ℝ :=
  (2⁻¹ : ENNReal) • Measure.dirac 0 + (2⁻¹ : ENNReal) • Measure.dirac 2

theorem int_ν (t : ℝ) : Integrable (fun x : ℝ => Real.exp (t * x)) ν :=
  ((int_dirac 0 t).smul_measure (by simp)).add_measure
    ((int_dirac 2 t).smul_measure (by simp))

theorem prob_ν : IsProbabilityMeasure ν := by
  constructor
  simp [ν, ENNReal.inv_two_add_inv_two]

theorem mgf_μ (t : ℝ) : mgf id (Measure.dirac (1 : ℝ)) t = Real.exp t := by
  unfold mgf
  rw [integral_dirac]
  simp

theorem mgf_ν (t : ℝ) : mgf id ν t = 1 / 2 + 1 / 2 * Real.exp (t * 2) := by
  unfold mgf ν
  simp only [id_eq]
  rw [integral_add_measure ((int_dirac 0 t).smul_measure (by simp))
    ((int_dirac 2 t).smul_measure (by simp)), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  simp

end MO202502

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_202502.main) := by
  intro h
  have key := h (Measure.dirac (1 : ℝ)) MO202502.ν inferInstance MO202502.prob_ν
    (fun t _ => ⟨MO202502.int_dirac 1 t, MO202502.int_ν t, by
      rw [MO202502.mgf_μ, MO202502.mgf_ν]
      have e : Real.exp (t * 2) = Real.exp t * Real.exp t := by
        rw [mul_two, Real.exp_add]
      nlinarith [sq_nonneg (Real.exp t - 1)]⟩) (1 / 2)
  have h1 : Measure.dirac (1 : ℝ) (Set.Ioi (1 / 2)) = 1 := by
    rw [Measure.dirac_apply' _ measurableSet_Ioi]
    norm_num [Set.indicator]
  have h2 : MO202502.ν (Set.Ioi (1 / 2)) = 2⁻¹ := by
    unfold MO202502.ν
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply' _ measurableSet_Ioi, Measure.dirac_apply' _ measurableSet_Ioi]
    norm_num [Set.indicator]
  rw [h1, h2] at key
  exact absurd key (not_le.mpr (ENNReal.inv_lt_one.mpr (by norm_num)))
