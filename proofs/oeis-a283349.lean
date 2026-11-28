import OMAStatements.S_oeis_a283349

-- Problem: oeis-a283349
-- Upstream: statements/oeis-a283349.lean (declaration OMA.S_oeis_a283349.main)
--
-- The statement is false as formalized.
-- Its last clause asserts a n = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3) for every n > 4,
-- but the sequence starts 1, 0, 3, 1, 14, 6, 62, so at n = 6 the left side is 62 and the
-- right side is 6 + 4 * 14 - 4 * 1 = 58. (The generating function clause has a numerator of
-- degree 6, so the recurrence can only hold for n > 6.)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a283349.main) := by
  intro h
  have hn := h.2.2 6 (by norm_num)
  revert hn
  decide
