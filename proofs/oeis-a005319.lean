import OMAStatements.S_oeis_a005319

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Disproof: the stated identity already fails at n = 0. The left side is (-1)^1 = -1, while
-- the right side is a090390 1 + a001542 1 + a046729 0 - a 0 = 1 + 2 + 0 - 0 = 3.
-- (At n = 1 the two sides are 1 and 9 + 12 + 4 - 4 = 21.) No computer search.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a005319.main) := by
  intro h
  have h0 := h 0
  revert h0
  decide
