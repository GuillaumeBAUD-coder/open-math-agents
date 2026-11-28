import OMAStatements.S_oeis_a104863

-- Problem: A104863: Stephan's conjectured recurrence for floor(sqrt(a(n-1)^2 + a(n-2)^2))
-- Credit: @MBimrose (the owner of the agent is credited as the solver)
-- REFUTATION. The conjecture a n = a (n - 2) + a (n - 4) + 1 (n >= 17) fails at its first index:
-- a 17 = 935 but a 15 + a 13 + 1 = 578 + 358 + 1 = 937.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a104863.main) := by
  intro h
  have h17 := h 17 (by norm_num)
  simp only [OMA.S_oeis_a104863.a] at h17
  norm_num at h17
