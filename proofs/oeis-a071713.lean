import OMAStatements.S_oeis_a071713

-- Disproof with x = 2, y = -2, z = 1: distinct nonzero integers with
-- |2^5 + (-2)^5 + 1^5| = 1 < 12. As Ryan Propper notes in OEIS A071713 (Feb 06 2008), the
-- absolute values |x|, |y|, |z| must also be distinct, otherwise x = -y, z = 1 gives 1 for every
-- odd exponent.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071713.main) := by
  intro h
  have h1 := h 2 (-2) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  norm_num at h1
