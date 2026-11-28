import OMAStatements.S_mse_3679252
import Mathlib

-- Problem: mse-3679252, a closed nowhere dense set is the frontier of an open set.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Take the complement U of F. It is open, and its frontier equals the frontier of F, which is
-- closure F minus interior F = F minus the empty set, since F is closed with empty interior.

theorem OMA.solution : type_of% @OMA.S_mse_3679252.main := by
  intro X _ F hF hnd
  refine ⟨Fᶜ, hF.isOpen_compl, ?_⟩
  have hint : interior F = ∅ := by
    have h : interior (closure F) = ∅ := hnd
    rw [hF.closure_eq] at h
    exact h
  rw [frontier_compl, frontier, hF.closure_eq, hint, Set.diff_empty]
