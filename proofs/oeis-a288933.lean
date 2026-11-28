import OMAStatements.S_oeis_a288933

-- The second conjunct asks 0 < 3 - a(n)/n < 1 for every n ≥ 1, but a(1) = 2,
-- so 3 - a(1)/1 = 1 and the strict upper bound fails at n = 1.
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a288933.main) := by
  intro h
  have ha : OMA.S_oeis_a288933.a 1 = 2 := by decide
  have h1 := (h.2.1 1 le_rfl).2
  rw [ha] at h1
  norm_num at h1
