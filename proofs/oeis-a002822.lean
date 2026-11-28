import OMAStatements.S_oeis_a002822

-- Problem: OEIS A002822, B. Selcoe's conjecture that 6j in the sequence forces j in it.
-- Disproof: j = 63. Here 6 * 378 - 1 = 2267 and 6 * 378 + 1 = 2269 are twin primes, so
-- 378 = 6 * 63 is a term, but 6 * 63 - 1 = 377 = 13 * 29 is composite, so 63 is not
-- (J. Kimberley, OEIS A002822, Oct 13 2015; the counterexamples form A263282).

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a002822.main) := by
  intro h
  have h63 := h 63 (by norm_num) ⟨by norm_num, by norm_num, by norm_num⟩
  have h377 : ¬ Nat.Prime (6 * 63 - 1) := by norm_num
  exact h377 h63.2.1
