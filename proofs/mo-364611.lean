import OMAStatements.S_mo_364611

-- Problem: Frechet-Urysohn quotient of second countable locally compact Hausdorff space
-- Upstream: formal-conjectures statements/mo-364611.lean:0 (declaration OMA.S_mo_364611.main)
-- The target allows both spaces to be empty.

theorem OMA.solution : type_of% @OMA.S_mo_364611.main := by
  exact ⟨Empty, Empty, inferInstance, inferInstance, id, inferInstance, inferInstance,
    inferInstance, Topology.IsQuotientMap.id, inferInstance, inferInstance, fun y => y.elim⟩
