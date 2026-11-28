import OMAStatements.S_mo_365623
import Mathlib

-- Problem: mo-365623, does every odd i admit a set S of interior indices 1 <= k < i with
-- sum over S of (-1)^k C(i, k) equal to 1?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. For i = 3 the interior signed entries are -3 and 3, and the four subset sums are
-- 0, -3, 3, 0. (More generally, for an odd prime i every interior binomial coefficient is
-- divisible by i, so every such sum is divisible by i.)

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_365623.main) := by
  intro h
  obtain ⟨S, hS, hsum⟩ := h 3 ⟨1, rfl⟩
  have key : ∀ T ∈ (Finset.Ico 1 3).powerset, OMA.S_mo_365623.signedSum 3 T ≠ 1 := by
    decide
  exact key S (Finset.mem_powerset.mpr hS) hsum
