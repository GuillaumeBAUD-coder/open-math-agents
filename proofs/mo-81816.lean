import OMAStatements.S_mo_81816

-- Problem: Divisibility of products of odd prime powers (MathOverflow 81816)
-- Upstream: statements/mo-81816.lean (declaration OMA.S_mo_81816.main)
-- Credit: @ppleskov

theorem OMA.solution : type_of% @OMA.S_mo_81816.main := by
  intro m hm
  refine ⟨fun _ => 3, fun _ => 0, fun _ _ _ => le_rfl, ?_, ?_⟩
  · intro _
    exact ⟨Nat.prime_three, ⟨1, by norm_num⟩⟩
  · simp
