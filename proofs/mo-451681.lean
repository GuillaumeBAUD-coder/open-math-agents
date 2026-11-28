import OMAStatements.S_mo_451681

-- Problem: Image of open set under a real analytic map is Borel?
-- Upstream: formal-conjectures statements/mo-451681.lean:0 (declaration OMA.S_mo_451681.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Set
open scoped Topology Manifold ContDiff

theorem OMA.solution : type_of% @OMA.S_mo_451681.main := by
  intro E E' _ _ _ _ _ _ M N _ _ _ _ _ _ _ _ _ _ _ _ f hf U hU
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  have h1 : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance
  have h2 : IsSigmaCompact (f '' U) := h1.image hf.continuous
  obtain ⟨K, hK, hKU⟩ := h2
  rw [← hKU]
  exact MeasurableSet.iUnion fun n => (hK n).isClosed.measurableSet
