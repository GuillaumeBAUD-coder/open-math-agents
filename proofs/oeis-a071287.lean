import OMAStatements.S_oeis_a071287

-- At index 6 the stream numerator is 1. The printed generating function
-- starts in degree 12, so its coefficient there is 0 (observed by @eliayousf).
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071287.main) :=
  fun h => nomatch h.2 6
