import OMAStatements.S_mo_178688

-- Problem: Set of distinct real numbers such that all combination of sums are distinct
-- Upstream: formal-conjectures statements/mo-178688.lean:0 (declaration OMA.S_mo_178688.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @OMA.S_mo_178688.main := by
  intro n x hx
  refine ⟨hx.injective, ?_⟩
  intro p u v _ _ h
  unfold OMA.S_mo_178688.combinationSum at h
  have h2 : ∑ i, (((u i : ℚ) - (v i : ℚ)) • x i) = 0 := by
    have key : ∀ i, ((u i : ℚ) - (v i : ℚ)) • x i = (u i : ℝ) * x i - (v i : ℝ) * x i := by
      intro i
      rw [Rat.smul_def]
      push_cast
      ring
    simp only [key, Finset.sum_sub_distrib, h, sub_self]
  have h3 := (Fintype.linearIndependent_iff.1 hx) (fun i => (u i : ℚ) - (v i : ℚ)) h2
  funext i
  have h4 := h3 i
  have h5 : (u i : ℚ) = v i := by linarith
  exact_mod_cast h5
