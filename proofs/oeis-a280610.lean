import OMAStatements.S_oeis_a280610

-- Problem: oeis-a280610
-- Upstream: statements/oeis-a280610.lean (declaration OMA.S_oeis_a280610.main)
--
-- The statement is false as formalized.
-- Its second clause asserts a n = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3) for every n > 4,
-- but the sequence starts 1, 3, 1, 7, 17, 39, 65, so at n = 6 the left side is 65 and the
-- right side is 2 * 39 + 17 - 2 * 7 = 81.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a280610.main) := by
  intro h
  have hn := h.2 6 (by norm_num)
  revert hn
  decide
