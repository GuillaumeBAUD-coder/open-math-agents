import OMAStatements.S_oeis_a102827
import Mathlib

namespace A102827Aux
lemma val4 : (OMA.S_oeis_a102827.state 2 4).1 = 2 := by decide
end A102827Aux

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a102827.main) := by
  intro h
  apply h 2 (le_refl 2) 4
  rw [A102827Aux.val4]
