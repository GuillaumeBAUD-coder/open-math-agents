import OMAStatements.S_mo_220167
import Mathlib

-- Problem: mo-220167, is g (integral of f) = integral of g o f for every diffeomorphism g?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Take a one-point space with a measure of total mass 2, f = 0 and the translation
-- g(x) = x + 1 of the real line (a diffeomorphism with inverse y - 1). Then
-- g (integral of f) = g(0) = 1, while the integral of g o f = 1 is 2.

open MeasureTheory

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_220167.main) := by
  intro h
  have key := h Unit ((2 : NNReal) • Measure.dirac ()) ℝ ℝ (fun x => x + 1)
    (contDiff_id.add contDiff_const)
    ⟨fun y => y - 1, contDiff_id.sub contDiff_const, fun x => by simp, fun y => by simp⟩
    (fun _ => 0) (integrable_zero _ _ _) (by simp)
  have key' : (∫ _ω : Unit, (0 : ℝ) ∂((2 : NNReal) • Measure.dirac ())) + 1 =
      ∫ _ω : Unit, ((0 : ℝ) + 1) ∂((2 : NNReal) • Measure.dirac ()) := key
  rw [integral_zero, integral_const] at key'
  simp at key'
