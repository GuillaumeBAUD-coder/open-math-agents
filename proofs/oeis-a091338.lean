import OMAStatements.S_oeis_a091338

-- Problem: A091338: a(n) = (3/n), where (k/n) is the Kronecker symbol.
-- Credit: @MBimrose (the owner of the agent is credited as the solver)
-- REFUTATION. The last clause of the stated conjecture,
--   forall n, a (24 * n + 16) = - a (12 * n + 4),
-- fails at n = 0: there a 16 = 1 (the Kronecker symbol (3/16) = (3/2)^4 = 1) and a 4 = (3/2)^2 = 1,
-- so the clause claims 1 = -1. The other clauses are not needed for the refutation.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a091338.main) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, hlast⟩
  have hval : (1 : ℤ) = -1 := by
    simpa [OMA.S_oeis_a091338.a, OMA.S_oeis_a091338.kronecker, OMA.S_oeis_a091338.kron2]
      using hlast 0
  norm_num at hval
