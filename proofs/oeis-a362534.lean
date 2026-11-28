import OMAStatements.S_oeis_a362534
import Mathlib

namespace OMA.S_oeis_a362534

lemma bad : ¬ ((g 19).num = ((f 19 / g 19).den : ℤ)) := by
  decide +kernel

end OMA.S_oeis_a362534

open OMA.S_oeis_a362534 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a362534.main) := by
  intro h
  exact bad (h 19 (by norm_num))
