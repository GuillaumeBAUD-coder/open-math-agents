import OMAStatements.S_mo_261486

-- Counterexample to MathOverflow 261486:
-- For n = 136 and prime q = 11, d(136) = 136^135 - 135^135 satisfies 11^3 | d(136)
-- (since 136^135 % 1331 = 980 = 135^135 % 1331, with exact valuation v_11(d(136)) = 3).

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_261486.main) :=
  fun h => h 136 (by decide) 11 (by decide) (by decide +kernel)
