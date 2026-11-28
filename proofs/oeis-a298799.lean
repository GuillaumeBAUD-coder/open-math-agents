import OMAStatements.S_oeis_a298799

open OMA.S_oeis_a298799

set_option maxRecDepth 60000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a298799.main) := fun h =>
  absurd (h 19 362 (by decide) (by decide) (by decide) fun ⟨m, k, hm, _, hk, _⟩ => by norm_num at hm hk; omega) (by decide +kernel)
