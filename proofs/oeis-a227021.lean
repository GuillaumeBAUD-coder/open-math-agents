import OMAStatements.S_oeis_a227021

-- Credit: @tjgksruf9801 (shorter proof). The claimed generating function at n = 8 and the
-- claimed recurrence at n = 1 are incompatible.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a227021.main) := fun h => by
  have e1 := h.1 8
  have e2 := h.2 1
  norm_num [OMA.S_oeis_a227021.lag, OMA.S_oeis_a227021.numerator] at e1 e2
  linarith
