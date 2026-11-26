import FormalConjectures.ErdosProblems.«834»

-- Problem: Erdős Problem 834 — ii
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/834.lean:60 (declaration Erdos834.erdos_834.parts.ii)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

/-- The 9-vertex 3-uniform hypergraph of R. Li (arXiv 2512.24850), vertices shifted down by one. -/
abbrev LiH : Finset (Finset (Fin 9)) :=
  {{0, 1, 2}, {0, 1, 8}, {0, 2, 7}, {0, 3, 5}, {0, 3, 7}, {0, 3, 8}, {0, 4, 6}, {0, 4, 7}, {0, 4, 8}, {0, 5, 6}, {1, 2, 5}, {1, 2, 6}, {1, 3, 8}, {1, 4, 8}, {1, 5, 6}, {2, 3, 7}, {2, 4, 7}, {2, 5, 6}, {3, 5, 7}, {3, 5, 8}, {4, 6, 7}, {4, 6, 8}}

theorem liH_not_two : ¬ ∃ c : Fin 9 → Fin 2, LiH.IsProperHypergraphColoring c := by
  unfold Finset.IsProperHypergraphColoring
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem liH_edge : ∀ e ∈ LiH, (LiH.erase e).HypergraphColorable 2 := by
  intro e he
  simp only [LiH, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨![1, 1, 1, 1, 1, 0, 0, 0, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![0, 0, 1, 1, 1, 1, 0, 0, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![0, 1, 0, 1, 1, 1, 0, 0, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![1, 1, 0, 1, 1, 1, 0, 0, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![1, 1, 0, 1, 0, 0, 1, 1, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![0, 1, 0, 0, 1, 1, 0, 1, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![1, 1, 0, 1, 1, 0, 1, 0, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![1, 1, 0, 0, 1, 1, 0, 1, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![0, 1, 0, 1, 0, 0, 1, 1, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![0, 1, 1, 1, 1, 0, 0, 0, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![0, 1, 1, 1, 1, 1, 0, 0, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![0, 1, 1, 1, 1, 0, 1, 0, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![1, 0, 1, 0, 1, 1, 0, 0, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![1, 0, 1, 1, 0, 0, 1, 0, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![1, 0, 1, 1, 1, 0, 0, 0, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![1, 1, 0, 0, 1, 1, 0, 0, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![1, 1, 0, 1, 0, 0, 1, 0, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![1, 1, 0, 1, 1, 0, 0, 0, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![0, 1, 0, 1, 1, 1, 0, 1, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![1, 1, 0, 0, 0, 0, 1, 1, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![0, 1, 0, 1, 1, 0, 1, 1, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · exact ⟨![1, 1, 0, 0, 0, 1, 0, 1, 0], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩

theorem vertex_of_edge {e : Finset (Fin 9)} {v : Fin 9} (hv : v ∈ e) (he : e ∈ LiH) :
    (LiH.filter (fun f ↦ v ∉ f)).HypergraphColorable 2 := by
  obtain ⟨c, hc⟩ := liH_edge e he
  refine ⟨c, fun f hf ↦ hc f ?_⟩
  rw [Finset.mem_filter] at hf
  rw [Finset.mem_erase]
  exact ⟨fun h ↦ hf.2 (h ▸ hv), hf.1⟩

end OMA

theorem OMA.solution : type_of% @Erdos834.erdos_834.parts.ii := by
  refine ⟨9, OMA.LiH, ?_, ⟨?_, ?_⟩, OMA.liH_edge, ?_, ?_⟩
  · unfold Finset.IsUniform; decide +kernel
  · exact ⟨![0, 0, 1, 0, 0, 1, 2, 1, 1], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩
  · intro j hj
    interval_cases j
    · rintro ⟨c, -⟩
      exact (c 0).elim0
    · rintro ⟨c, hc⟩
      obtain ⟨x, -, y, -, hxy⟩ := hc {0, 1, 2} (by decide +kernel)
      exact hxy (Subsingleton.elim _ _)
    · exact OMA.liH_not_two
  · intro v
    fin_cases v
    · exact OMA.vertex_of_edge (e := {0, 1, 2}) (by decide +kernel) (by decide +kernel)
    · exact OMA.vertex_of_edge (e := {0, 1, 2}) (by decide +kernel) (by decide +kernel)
    · exact OMA.vertex_of_edge (e := {0, 1, 2}) (by decide +kernel) (by decide +kernel)
    · exact OMA.vertex_of_edge (e := {0, 3, 5}) (by decide +kernel) (by decide +kernel)
    · exact OMA.vertex_of_edge (e := {0, 4, 6}) (by decide +kernel) (by decide +kernel)
    · exact OMA.vertex_of_edge (e := {0, 3, 5}) (by decide +kernel) (by decide +kernel)
    · exact OMA.vertex_of_edge (e := {0, 4, 6}) (by decide +kernel) (by decide +kernel)
    · exact OMA.vertex_of_edge (e := {0, 2, 7}) (by decide +kernel) (by decide +kernel)
    · exact OMA.vertex_of_edge (e := {0, 1, 8}) (by decide +kernel) (by decide +kernel)
  · intro v
    unfold Finset.hypergraphDegree
    revert v
    decide +kernel
