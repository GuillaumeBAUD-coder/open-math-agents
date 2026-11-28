import OMAStatements.S_oeis_a362534
import Mathlib

-- Counterexample n = 19 (the refutation the statement cites): g(19) = 215955/131072, while
-- f(19)/g(19) = 92378/43191, so the numerator of g(19) is 215955, not 43191.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a362534.main) := by
  intro h
  have h19 := h 19 (by norm_num)
  revert h19
  decide +kernel
