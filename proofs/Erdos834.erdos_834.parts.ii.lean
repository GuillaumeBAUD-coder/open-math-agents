import FormalConjectures.ErdosProblems.«834»

-- Problem: Erdős Problem 834 — ii
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/834.lean:60 (declaration Erdos834.erdos_834.parts.ii)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- The 9-vertex 3-uniform hypergraph of R. Li (arXiv 2512.24850), vertices shifted down by one; every
-- property (uniformity, colorings, criticality, degrees) is decided by the kernel.

set_option maxHeartbeats 0 in
theorem OMA.solution : type_of% @Erdos834.erdos_834.parts.ii := by
  refine ⟨9, {{0, 1, 2}, {0, 1, 8}, {0, 2, 7}, {0, 3, 5}, {0, 3, 7}, {0, 3, 8}, {0, 4, 6}, {0, 4, 7}, {0, 4, 8}, {0, 5, 6}, {1, 2, 5}, {1, 2, 6}, {1, 3, 8}, {1, 4, 8}, {1, 5, 6}, {2, 3, 7}, {2, 4, 7}, {2, 5, 6}, {3, 5, 7}, {3, 5, 8}, {4, 6, 7}, {4, 6, 8}}, ?_, ⟨⟨![0, 0, 1, 0, 0, 1, 2, 1, 1], ?_⟩, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp only [Finset.IsUniform, Finset.HypergraphColorable, Finset.IsProperHypergraphColoring, Finset.hypergraphDegree] <;>
    decide +kernel
