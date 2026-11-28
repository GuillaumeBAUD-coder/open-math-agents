import OMAStatements.S_oeis_a384162

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Disproof: the identity fails at n = 2. The four binary words of length 2 have run-length
-- products 2, 1, 1, 2, so markedWords 2 = 6, while 2 * companion 1 = 2 * scaledU 4 1 = 8.
-- (Kernel evaluation of these small finite sums; no other computer search.)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a384162.main) := by
  intro h
  have h2 := h 2 (by norm_num)
  revert h2
  decide +kernel
