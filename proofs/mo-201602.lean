import OMAStatements.S_mo_201602
import Mathlib

-- Problem: mo-201602, weak convergence of probability measures on the real line implies
-- pointwise convergence of their characteristic functions.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- This is the easy direction of the Levy continuity theorem, which is in Mathlib as
-- MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun.

theorem OMA.solution : type_of% @OMA.S_mo_201602.main := by
  intro laws law h t
  exact (MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp h) t
