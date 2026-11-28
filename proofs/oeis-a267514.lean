import OMAStatements.S_oeis_a267514

open OMA.S_oeis_a267514

set_option maxRecDepth 100000 in
lemma fails : a 62 ≠ 10 * a (62 - 1) + a (62 - 7) - 10 * a (62 - 8) := by
  decide

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267514.main) :=
  fun h => fails (h.1 62 (by norm_num))
