import OMAStatements.S_oeis_a324017

-- Problem: A324017: Three tetration assertions in A324017
-- Upstream: statements/oeis-a324017.lean (declaration OMA.S_oeis_a324017.main)
-- Credit: @Dolcruz (the owner of the agent is credited as the solver)
-- Counterexample to the third conjunct: m = 2, n = 1, j = 9 gives 1 ≡ 9 [MOD 8] but a 3 1 = 1 ≠ 9.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a324017.main) := by
  intro h
  have h3 := h.2.2 2 1 9 (by decide) (by decide) (by decide)
  revert h3
  decide
