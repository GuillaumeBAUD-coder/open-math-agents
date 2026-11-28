import OMAStatements.S_oeis_a272766

-- Credit: @tjgksruf9801 (shorter proof). primorial 11 = 2310 is not a term: m = 37 < 2309
-- already gives (2 * 2310) ^ 2 - 1 ∣ (2 ^ 37) ^ (2 * 2310) - 1.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a272766.main) := fun h =>
  (h 11 (by decide)).2.2 37 (by decide) (by decide) (by decide +kernel)
