import FormalConjectures.ErdosProblems.«554»

/-! With one colour, the Ramsey threshold is the number of vertices in the cycle.
The original proof was submitted by @eitanteperman. -/

open SimpleGraph

theorem OMA.solution : type_of% @Erdos554.multicolourGraphRamsey_one_cycleGraph_five := by
  unfold multicolourGraphRamsey
  refine IsLeast.csInf_eq ⟨?_, ?_⟩
  · intro C
    refine ⟨0, .of_le fun _ _ h ↦ ?_⟩
    rw [TopEdgeLabeling.labelGraph_adj]
    exact ⟨h.ne, Subsingleton.elim _ _⟩
  · intro n hn
    obtain ⟨_, ⟨f⟩⟩ := hn (EdgeLabeling.mk (fun _ _ _ ↦ 0) (fun _ _ _ ↦ rfl))
    simpa using Fintype.card_le_of_embedding f.toEmbedding
