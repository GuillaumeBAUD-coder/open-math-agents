import OMAStatements.S_mo_201602
import Mathlib

/-!
MathOverflow 201602: the direction asked for is immediate from the definition of weak
convergence, because `x ↦ exp (i t x)` is a bounded continuous function
(`ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto` with `𝕜 = ℂ`).
-/

namespace OMA.P201602

open Filter MeasureTheory Complex
open scoped Topology BoundedContinuousFunction

/-- `x ↦ exp (i x t)` as a bounded continuous function. -/
noncomputable def expB (t : ℝ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => exp ((t : ℂ) * x * I), by fun_prop⟩ 2 (fun x y => by
      have hn : ∀ z : ℝ, ‖exp ((t : ℂ) * z * I)‖ = 1 := fun z => by
        rw [show (t : ℂ) * z * I = ((t * z : ℝ) : ℂ) * I by push_cast; ring,
          norm_exp_ofReal_mul_I]
      simp only [ContinuousMap.coe_mk]
      calc dist (exp ((t : ℂ) * x * I)) (exp ((t : ℂ) * y * I))
          ≤ ‖exp ((t : ℂ) * x * I)‖ + ‖exp ((t : ℂ) * y * I)‖ := dist_le_norm_add_norm _ _
        _ = 2 := by rw [hn, hn]; norm_num)

theorem proof_aux : ∀ (laws : ℕ → ProbabilityMeasure ℝ) (law : ProbabilityMeasure ℝ),
    Tendsto laws atTop (𝓝 law) →
    ∀ t : ℝ, Tendsto (fun n => charFun (laws n : Measure ℝ) t) atTop
      (𝓝 (charFun (law : Measure ℝ) t)) := by
  intro laws law h t
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 h (expB t)
  simpa [expB, charFun_apply_real] using this

end OMA.P201602

theorem OMA.solution : type_of% @OMA.S_mo_201602.main := OMA.P201602.proof_aux
