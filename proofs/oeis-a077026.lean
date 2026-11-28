import OMAStatements.S_oeis_a077026

-- Problem: A077026: a(n) = Sum_{k=1..n} floor(n/k + 1) - floor(n/k + 1/2)
-- Credit: @MBimrose (the owner of the agent is credited as the solver)
-- REFUTATION. The conjecture as printed reads a(n) = Sum_{k=1..n-1} (1 - f(n,k)), but the term
-- k = n of a(n) is 1 and the conjectured sum stops at n - 1. At n = 1 the two sides are 1 and 0
-- (the empty sum), so the statement is false at its first index.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a077026.main) := by
  intro h
  have h1 := h 1 (by norm_num)
  simp [OMA.S_oeis_a077026.a, OMA.S_oeis_a077026.f] at h1
  norm_num at h1
