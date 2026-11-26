import FormalConjectures.ErdosProblems.«554»

-- Problem: Erdős Problem 554 — multicolourGraphRamsey one cycleGraph five
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/554.lean:70 (declaration Erdos554.multicolourGraphRamsey_one_cycleGraph_five)
-- Credit: @eitanteperman (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open SimpleGraph

theorem OMA.solution : type_of% @Erdos554.multicolourGraphRamsey_one_cycleGraph_five := by
  unfold multicolourGraphRamsey
  have h5 : 5 ∈ {n : ℕ | ∀ C : TopEdgeLabeling (Fin n) (Fin 1),
      ∃ i, (cycleGraph 5).IsContained (C.labelGraph i)} := by
    intro C
    refine ⟨0, ?_⟩
    rw [isContained_iff_exists_le_comap]
    refine ⟨Function.Embedding.refl _, fun x y hxy => ?_⟩
    simp only [comap_adj, Function.Embedding.refl_apply, TopEdgeLabeling.labelGraph_adj]
    exact ⟨hxy.ne, Subsingleton.elim _ _⟩
  apply le_antisymm (Nat.sInf_le h5)
  apply le_csInf ⟨5, h5⟩
  intro n hn
  by_contra hlt
  obtain ⟨i, hi⟩ := hn (EdgeLabeling.mk (fun _ _ _ => 0) (fun _ _ _ => rfl))
  rw [isContained_iff_exists_le_comap] at hi
  obtain ⟨f, -⟩ := hi
  have := Fintype.card_le_of_embedding f
  simp at this
  omega
